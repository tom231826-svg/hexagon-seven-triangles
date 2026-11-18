import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0094
import HexagonCover.NBand.M8500_8700.SplitTree.Run0096
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0097
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip6770_6812 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6812 ![1237940039285380274899124609, 619121135372464684410078722, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0096.checked6812
def Tip6770_6773 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6773 ![1856910058928070412348686721, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0096.checked6773
def Tip6770_6911 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6911 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0096.checked6911
def Tip6770_6931 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6931 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0096.checked6931
def B6910 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5992156713056701964635107814136760380589323426226184, 365375409332725729867833858236128105288159035408, 1730417938599789055153162841936079095272624131276832, 3005578128364973128812934669880140037824351085002816] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1064).pointIds 1064), (.leaf 4 (Common.fact 1104).pointIds 1104), (.leaf 5 (Common.fact 1047).pointIds 1047), (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq6910 : B6910.tree = HexagonCover.NBand.M8500_8700.SplitData.node6910 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6909 : Block := .branch 162 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 365375409332725729867833858236128105288159035408, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B6910, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6909 : B6909.tree = HexagonCover.NBand.M8500_8700.SplitData.node6909 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6910
  · rfl
  · rfl
  · rfl

def B6908 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 365375409332725729867833858236128105288159035408, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![B6909, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq6908 : B6908.tree = HexagonCover.NBand.M8500_8700.SplitData.node6908 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6909
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6907 : Block := .branch 101 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 365375409332725729867833858236128105288159035408, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![B6908, (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 1099).pointIds 1099), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 1102).pointIds 1102), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq6907 : B6907.tree = HexagonCover.NBand.M8500_8700.SplitData.node6907 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6908
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6906 : Block := .branch 114 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 365375409332725729867833858236128105288159035408, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![B6907, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq6906 : B6906.tree = HexagonCover.NBand.M8500_8700.SplitData.node6906 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6907
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6905 : Block := .branch 158 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 316912650057057350374175899664, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6906, (.leaf 5 (Common.fact 1092).pointIds 1092), (.leaf 0 [] 0)]
theorem treeEq6905 : B6905.tree = HexagonCover.NBand.M8500_8700.SplitData.node6905 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6906
  · rfl
  · rfl

def B6904 : Block := .branch 88 ![748288838313422294120287872290776191444112361128321, 618970019644942487019062786, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 316912650057057350374175899664, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 1096).pointIds 1096), B6905, (.leaf 2 (Common.fact 1097).pointIds 1097), (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6904 : B6904.tree = HexagonCover.NBand.M8500_8700.SplitData.node6904 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6905
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6903 : Block := .branch 160 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835703278458516698830852, 5986310706507378352962293074805895248510699696054280, 316912650057057350374175899664, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6904, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 1091).pointIds 1091)]
theorem treeEq6903 : B6903.tree = HexagonCover.NBand.M8500_8700.SplitData.node6903 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6904
  · rfl
  · rfl
  · rfl
  · rfl

def B6902 : Block := .branch 171 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4873482210321473860540420, 5986310706507378352962293074805895248510699696054280, 1329228312697565929961157434456244240, 1730417938599789055153162841936079095272624131276832, 12422775143951059556198224969676375882450985287744] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6903]
theorem treeEq6902 : B6902.tree = HexagonCover.NBand.M8500_8700.SplitData.node6902 := by
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
  · exact treeEq6903

def B6901 : Block := .branch 172 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4873482210321473860540420, 24584, 1329228312697565929961157434456244240, 1730417938599789055153162841936079095272624131276832, 12422775143951059556198224969676375882450985287744] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6902, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq6901 : B6901.tree = HexagonCover.NBand.M8500_8700.SplitData.node6901 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6902
  · rfl
  · rfl
  · rfl

def B6900 : Block := .branch 159 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4873482210321473860540420, 24584, 1329228312697565929961157434456244240, 1730417938599789055153162841936079095272624131276832, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 1095).pointIds 1095), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6901]
theorem treeEq6900 : B6900.tree = HexagonCover.NBand.M8500_8700.SplitData.node6900 := by
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
  · exact treeEq6901

def B6899 : Block := .branch 169 ![1237940039285380274899124609, 619121135372464684410078722, 4873482210321473860540420, 158456325028528675187087925256, 1329228312697565929961157434456244240, 1730417938599789055153162841936079095272624131276832, 11692024325285608097096382553318234372623019016256] ![B6900, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6899 : B6899.tree = HexagonCover.NBand.M8500_8700.SplitData.node6899 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6900
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6898 : Block := .branch 170 ![1237940039285380274899124609, 619121135372464684410078722, 4873482210321473860540420, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6899, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6898 : B6898.tree = HexagonCover.NBand.M8500_8700.SplitData.node6898 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6899
  · rfl

def B6897 : Block := .branch 163 ![1237940039285380274899124609, 619121135372464684410078722, 4873482210321473860540420, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6898]
theorem treeEq6897 : B6897.tree = HexagonCover.NBand.M8500_8700.SplitData.node6897 := by
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
  · exact treeEq6898

def B6896 : Block := .branch 165 ![1237940039285380274899124609, 619121135372464684410078722, 4873482210321473860540420, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6897, (.leaf 0 [] 0)]
theorem treeEq6896 : B6896.tree = HexagonCover.NBand.M8500_8700.SplitData.node6896 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6897
  · rfl

def B6895 : Block := .branch 167 ![1237940039285380274899124609, 619121135372464684410078722, 4873482210321473860540420, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6896, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6895 : B6895.tree = HexagonCover.NBand.M8500_8700.SplitData.node6895 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6896
  · rfl

def B6811 : Block := .branch 98 ![1237940039285380274899124609, 619121135372464684410078722, 130601785896986981739534340, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), Tip6770_6812, B6895, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6811 : B6811.tree = HexagonCover.NBand.M8500_8700.SplitData.node6811 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6895
  · rfl
  · rfl

def B6772 : Block := .branch 89 ![1237940039285380274899124609, 151115729774546960516610, 130601785896986981739534340, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![Tip6770_6773, B6811, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6772 : B6772.tree = HexagonCover.NBand.M8500_8700.SplitData.node6772 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6811
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6771 : Block := .branch 86 ![1237940039285380274899124609, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B6772, Tip6770_6911, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq6771 : B6771.tree = HexagonCover.NBand.M8500_8700.SplitData.node6771 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6772
  · rfl
  · rfl
  · rfl
  · rfl

def B6770 : Block := .branch 85 ![1237940039285380274899124609, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B6771, Tip6770_6931, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq6770 : B6770.tree = HexagonCover.NBand.M8500_8700.SplitData.node6770 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6771
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6770 : B6770.accepted = true := by decide +kernel
theorem checked6770 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6770 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6770]
  exact B6770.sound accepted6770
#print axioms checked6770

def B6970 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143559528134108298717339607048, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1116).pointIds 1116), (.leaf 4 (Common.fact 1040).pointIds 1040), (.leaf 5 (Common.fact 1026).pointIds 1026), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq6970 : B6970.tree = HexagonCover.NBand.M8500_8700.SplitData.node6970 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6969 : Block := .branch 98 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826646878077050948343163805704, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6970, (.leaf 4 (Common.fact 1113).pointIds 1113), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6969 : B6969.tree = HexagonCover.NBand.M8500_8700.SplitData.node6969 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6970
  · rfl
  · rfl
  · rfl

def B6968 : Block := .branch 108 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826646878077050948343163805704, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B6969, (.leaf 4 (Common.fact 1112).pointIds 1112), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6968 : B6968.tree = HexagonCover.NBand.M8500_8700.SplitData.node6968 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6969
  · rfl
  · rfl
  · rfl

def B6967 : Block := .branch 119 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826646878077050948343163805704, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B6968, (.leaf 4 (Common.fact 1111).pointIds 1111), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq6967 : B6967.tree = HexagonCover.NBand.M8500_8700.SplitData.node6967 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6968
  · rfl
  · rfl
  · rfl

def B6966 : Block := .branch 129 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826646878077050948343163805704, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B6967, (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq6966 : B6966.tree = HexagonCover.NBand.M8500_8700.SplitData.node6966 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6967
  · rfl
  · rfl
  · rfl

def B6965 : Block := .branch 138 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310795710359147084785660291581452938212515274760, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B6966, (.leaf 4 (Common.fact 1109).pointIds 1109), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq6965 : B6965.tree = HexagonCover.NBand.M8500_8700.SplitData.node6965 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6966
  · rfl
  · rfl
  · rfl

def B6964 : Block := .branch 146 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293094148708362344766491353096, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B6965, (.leaf 4 (Common.fact 1108).pointIds 1108), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq6964 : B6964.tree = HexagonCover.NBand.M8500_8700.SplitData.node6964 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6965
  · rfl
  · rfl
  · rfl

def B6963 : Block := .branch 162 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 805).pointIds 805), B6964, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6963 : B6963.tree = HexagonCover.NBand.M8500_8700.SplitData.node6963 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6964
  · rfl
  · rfl

def B6962 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6963, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6962 : B6962.tree = HexagonCover.NBand.M8500_8700.SplitData.node6962 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6963
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6961 : Block := .branch 101 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6962, (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 1099).pointIds 1099), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 1102).pointIds 1102), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq6961 : B6961.tree = HexagonCover.NBand.M8500_8700.SplitData.node6961 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6960 : Block := .branch 114 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6961, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq6960 : B6960.tree = HexagonCover.NBand.M8500_8700.SplitData.node6960 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6961
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6959 : Block := .branch 88 ![748288838313422294120287872290776191444112361128321, 618970019644942487019062786, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1096).pointIds 1096), B6960, (.leaf 2 (Common.fact 1097).pointIds 1097), (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6959 : B6959.tree = HexagonCover.NBand.M8500_8700.SplitData.node6959 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6960
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6958 : Block := .branch 160 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962451550473736891019953579253768, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6959, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6958 : B6958.tree = HexagonCover.NBand.M8500_8700.SplitData.node6958 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6959
  · rfl
  · rfl
  · rfl
  · rfl

def B6957 : Block := .branch 158 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962451550473736891019953579253768, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6958, (.leaf 5 (Common.fact 1012).pointIds 1012), (.leaf 0 [] 0)]
theorem treeEq6957 : B6957.tree = HexagonCover.NBand.M8500_8700.SplitData.node6957 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6958
  · rfl
  · rfl

def B6956 : Block := .branch 89 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310706507378352962451550473736891019953579253768, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1106).pointIds 1106), B6957, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6956 : B6956.tree = HexagonCover.NBand.M8500_8700.SplitData.node6956 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6957
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6955 : Block := .branch 172 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6956, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6955 : B6955.tree = HexagonCover.NBand.M8500_8700.SplitData.node6955 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6956
  · rfl
  · rfl
  · rfl

def B6954 : Block := .branch 159 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 1095).pointIds 1095), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6955]
theorem treeEq6954 : B6954.tree = HexagonCover.NBand.M8500_8700.SplitData.node6954 := by
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
  · exact treeEq6955

def B6953 : Block := .branch 169 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![B6954, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6953 : B6953.tree = HexagonCover.NBand.M8500_8700.SplitData.node6953 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6954
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6952 : Block := .branch 170 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6953, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6952 : B6952.tree = HexagonCover.NBand.M8500_8700.SplitData.node6952 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6953
  · rfl

def B6951 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6952]
theorem treeEq6951 : B6951.tree = HexagonCover.NBand.M8500_8700.SplitData.node6951 := by
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
  · exact treeEq6952

theorem accepted6951 : B6951.accepted = true := by decide +kernel
theorem checked6951 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6951 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6951]
  exact B6951.sound accepted6951
#print axioms checked6951

def B6990 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1118).pointIds 1118), (.leaf 4 (Common.fact 1040).pointIds 1040), (.leaf 5 (Common.fact 1026).pointIds 1026), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq6990 : B6990.tree = HexagonCover.NBand.M8500_8700.SplitData.node6990 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6989 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![B6990, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6989 : B6989.tree = HexagonCover.NBand.M8500_8700.SplitData.node6989 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6990
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6988 : Block := .branch 101 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![B6989, (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 1099).pointIds 1099), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 1102).pointIds 1102), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq6988 : B6988.tree = HexagonCover.NBand.M8500_8700.SplitData.node6988 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6989
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6987 : Block := .branch 114 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![B6988, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq6987 : B6987.tree = HexagonCover.NBand.M8500_8700.SplitData.node6987 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6988
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6986 : Block := .branch 88 ![748288838313422294120287872290776191444112361128321, 618970019644942487019062786, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 1096).pointIds 1096), B6987, (.leaf 2 (Common.fact 1097).pointIds 1097), (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6986 : B6986.tree = HexagonCover.NBand.M8500_8700.SplitData.node6986 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6985 : Block := .branch 160 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835703278458516698830852, 5986310796058808290812143549856727551381683941957640, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6986, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6985 : B6985.tree = HexagonCover.NBand.M8500_8700.SplitData.node6985 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6986
  · rfl
  · rfl
  · rfl
  · rfl

def B6984 : Block := .branch 158 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835703278458516698830852, 5986310796058808290812143549856727551381683941957640, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6985, (.leaf 5 (Common.fact 1012).pointIds 1012), (.leaf 0 [] 0)]
theorem treeEq6984 : B6984.tree = HexagonCover.NBand.M8500_8700.SplitData.node6984 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6985
  · rfl
  · rfl

def B6983 : Block := .branch 89 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835703278458516698830852, 5986310796058808290812143549856727551381683941957640, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1106).pointIds 1106), B6984, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6983 : B6983.tree = HexagonCover.NBand.M8500_8700.SplitData.node6983 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6984
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6982 : Block := .branch 98 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310796058808290811826637206670494031309766156296, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6983, (.leaf 4 (Common.fact 732).pointIds 732), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6982 : B6982.tree = HexagonCover.NBand.M8500_8700.SplitData.node6982 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6983
  · rfl
  · rfl
  · rfl

def B6981 : Block := .branch 108 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310796058808290811826637206670494031309766156296, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B6982, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6981 : B6981.tree = HexagonCover.NBand.M8500_8700.SplitData.node6981 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6982
  · rfl
  · rfl
  · rfl

def B6980 : Block := .branch 119 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310796058808290811826637206670494031309766156296, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B6981, (.leaf 4 (Common.fact 786).pointIds 786), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq6980 : B6980.tree = HexagonCover.NBand.M8500_8700.SplitData.node6980 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6981
  · rfl
  · rfl
  · rfl

def B6979 : Block := .branch 129 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310796058808290811826637206670494031309766156296, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B6980, (.leaf 4 (Common.fact 785).pointIds 785), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq6979 : B6979.tree = HexagonCover.NBand.M8500_8700.SplitData.node6979 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6980
  · rfl
  · rfl
  · rfl

def B6978 : Block := .branch 138 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310795710359147084785650620174896021179117625352, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B6979, (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq6978 : B6978.tree = HexagonCover.NBand.M8500_8700.SplitData.node6978 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6979
  · rfl
  · rfl
  · rfl

def B6977 : Block := .branch 146 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310706507378352962293084477301805427733093703688, 5846006549323611672814739330865132078623730270224, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B6978, (.leaf 4 (Common.fact 783).pointIds 783), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq6977 : B6977.tree = HexagonCover.NBand.M8500_8700.SplitData.node6977 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6978
  · rfl
  · rfl
  · rfl

def B6976 : Block := .branch 162 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310706507378352962293084477301805427733093703688, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 1117).pointIds 1117), B6977, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6976 : B6976.tree = HexagonCover.NBand.M8500_8700.SplitData.node6976 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6977
  · rfl
  · rfl

def B6975 : Block := .branch 172 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 9671406556917033397673992, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6976, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6975 : B6975.tree = HexagonCover.NBand.M8500_8700.SplitData.node6975 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6976
  · rfl
  · rfl
  · rfl

def B6974 : Block := .branch 159 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 9671406556917033397673992, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 1095).pointIds 1095), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6975]
theorem treeEq6974 : B6974.tree = HexagonCover.NBand.M8500_8700.SplitData.node6974 := by
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
  · exact treeEq6975

def B6973 : Block := .branch 169 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158465996435085592220485574664, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![B6974, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6973 : B6973.tree = HexagonCover.NBand.M8500_8700.SplitData.node6973 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6974
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6972 : Block := .branch 170 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6973, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6972 : B6972.tree = HexagonCover.NBand.M8500_8700.SplitData.node6972 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6973
  · rfl

def B6971 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6972]
theorem treeEq6971 : B6971.tree = HexagonCover.NBand.M8500_8700.SplitData.node6971 := by
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
  · exact treeEq6972

theorem accepted6971 : B6971.accepted = true := by decide +kernel
theorem checked6971 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6971 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6971]
  exact B6971.sound accepted6971
#print axioms checked6971

def Tip6482_6579 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6579 ![1238242270740283932192801153, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0094.checked6579
def Tip6482_6483 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6483 ![1238242270740283932192801153, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0094.checked6483
def B6760 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6760 : B6760.tree = HexagonCover.NBand.M8500_8700.SplitData.node6760 := by
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

def B6759 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6760, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6759 : B6759.tree = HexagonCover.NBand.M8500_8700.SplitData.node6759 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6760
  · rfl

def B6758 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6759]
theorem treeEq6758 : B6758.tree = HexagonCover.NBand.M8500_8700.SplitData.node6758 := by
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
  · exact treeEq6759

def B6578 : Block := .branch 85 ![1238242270740283932192801153, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), Tip6482_6579, B6758, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq6578 : B6578.tree = HexagonCover.NBand.M8500_8700.SplitData.node6578 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6758
  · rfl
  · rfl
  · rfl

def B6763 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6763 : B6763.tree = HexagonCover.NBand.M8500_8700.SplitData.node6763 := by
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

def B6762 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6763, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6762 : B6762.tree = HexagonCover.NBand.M8500_8700.SplitData.node6762 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6763
  · rfl

def B6761 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6762]
theorem treeEq6761 : B6761.tree = HexagonCover.NBand.M8500_8700.SplitData.node6761 := by
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
  · exact treeEq6762

def B6577 : Block := .branch 84 ![1238242270740283932192801153, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B6578, B6761, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq6577 : B6577.tree = HexagonCover.NBand.M8500_8700.SplitData.node6577 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6578
  · exact treeEq6761
  · rfl
  · rfl
  · rfl

def B6766 : Block := .branch 169 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6766 : B6766.tree = HexagonCover.NBand.M8500_8700.SplitData.node6766 := by
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

def B6765 : Block := .branch 170 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6766, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6765 : B6765.tree = HexagonCover.NBand.M8500_8700.SplitData.node6765 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6766
  · rfl

def B6764 : Block := .branch 171 ![1238242270740283932192801153, 151115729774546960516610, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6765]
theorem treeEq6764 : B6764.tree = HexagonCover.NBand.M8500_8700.SplitData.node6764 := by
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
  · exact treeEq6765

def B6576 : Block := .branch 83 ![1238242270740283932192801153, 151115729774546960516610, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B6577, B6764, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq6576 : B6576.tree = HexagonCover.NBand.M8500_8700.SplitData.node6576 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6577
  · exact treeEq6764
  · rfl
  · rfl
  · rfl

def B6482 : Block := .branch 82 ![1238242270740283932192801153, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), Tip6482_6483, B6576, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq6482 : B6482.tree = HexagonCover.NBand.M8500_8700.SplitData.node6482 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6576
  · rfl
  · rfl
  · rfl

theorem accepted6482 : B6482.accepted = true := by decide +kernel
theorem checked6482 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6482 (maskNeeds ![1238242270740283932192801153, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq6482]
  exact B6482.sound accepted6482
#print axioms checked6482

end HexagonCover.NBand.M8500_8700.SplitTree.Run0097
