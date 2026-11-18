import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0094
import HexagonCover.NBand.M8500_8700.SplitTree.Run0095
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0096
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip6812_6815 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6815 ![1268888540267514781771602329985, 928606145193809753134859778, 130601767450242908029982724, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0095.checked6815
def B6889 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5992156713056701964635107814136760380589323426226184, 365375409332726054069474866605797538070003810320, 1730417938599789055153162841936079095272624131276832, 3005578128364973128812934669880140037824351085002816] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1064).pointIds 1064), (.leaf 4 (Common.fact 1094).pointIds 1094), (.leaf 5 (Common.fact 1047).pointIds 1047), (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq6889 : B6889.tree = HexagonCover.NBand.M8500_8700.SplitData.node6889 := by
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

def B6888 : Block := .branch 162 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 365375409332726054069474866605797538070003810320, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B6889, (.leaf 4 (Common.fact 712).pointIds 712), (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6888 : B6888.tree = HexagonCover.NBand.M8500_8700.SplitData.node6888 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6889
  · rfl
  · rfl
  · rfl

def B6887 : Block := .branch 158 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310706507378352962293074805895248510699696054280, 324518553658426726783156020674576, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6888, (.leaf 5 (Common.fact 1092).pointIds 1092), (.leaf 0 [] 0)]
theorem treeEq6887 : B6887.tree = HexagonCover.NBand.M8500_8700.SplitData.node6887 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6888
  · rfl
  · rfl

def B6886 : Block := .branch 160 ![748288838313422294121554284950965135465334165209473, 928606145193809753134859778, 4835703278458516698830852, 5986310706507378352962293074805895248510699696054280, 324518553658426726783156020674576, 1730417938599789055153162841936079095272624131276832, 3005578128397640236037344762372624000137800833302592] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6887, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 1091).pointIds 1091)]
theorem treeEq6886 : B6886.tree = HexagonCover.NBand.M8500_8700.SplitData.node6886 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6887
  · rfl
  · rfl
  · rfl
  · rfl

def B6885 : Block := .branch 171 ![748288838313422294121555522891004420845609064333697, 928606145193809753134859778, 4873482210321473860540420, 5986310706507378352962609987455952305861073871855624, 1329552514338574299630590216301019152, 1730417938599789055153162841936079095272624131276832, 12422775143951059556198224969676375882450985287744] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6886]
theorem treeEq6885 : B6885.tree = HexagonCover.NBand.M8500_8700.SplitData.node6885 := by
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
  · exact treeEq6886

def B6884 : Block := .branch 172 ![748288838313422294121555522891004420845609064333697, 928606145193809753134859778, 4873482210321473860540420, 316912650057057350374175825928, 1329552514338574299630590216301019152, 1730417938599789055153162841936079095272624131276832, 12422775143951059556198224969676375882450985287744] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6885, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq6884 : B6884.tree = HexagonCover.NBand.M8500_8700.SplitData.node6884 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6885
  · rfl
  · rfl
  · rfl

def B6883 : Block := .branch 159 ![748288838313422294121555522891004420845609064333697, 928606145193809753134859778, 4873482210321473860540420, 316912650057057350374175825928, 1329552514338574299630590216301019152, 1730417938599789055153162841936079095272624131276832, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 1083).pointIds 1083), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6884]
theorem treeEq6883 : B6883.tree = HexagonCover.NBand.M8500_8700.SplitData.node6883 := by
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
  · exact treeEq6884

def B6882 : Block := .branch 169 ![1268888540267514781771602329985, 928606145193809753134859778, 4873482210321473860540420, 475368975085586025561263726600, 1329552514338574299630590216301019152, 1730417938599789055153162841936079095272624131276832, 11692024325285608097096382553318234372623019016256] ![B6883, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6882 : B6882.tree = HexagonCover.NBand.M8500_8700.SplitData.node6882 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6883
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6881 : Block := .branch 170 ![1268888540267514781771602329985, 928606145193809753134859778, 4873482210321473860540420, 475368975085586025561263726600, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11692024325285608097096382553318234372623019016256] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6882, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6881 : B6881.tree = HexagonCover.NBand.M8500_8700.SplitData.node6881 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6882
  · rfl

def B6880 : Block := .branch 163 ![1268888540267514781771602329985, 928606145193809753134859778, 4873482210321473860540420, 475368975085586025561263726600, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B6881]
theorem treeEq6880 : B6880.tree = HexagonCover.NBand.M8500_8700.SplitData.node6880 := by
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
  · exact treeEq6881

def B6879 : Block := .branch 165 ![1268888540267514781771602329985, 928606145193809753134859778, 4873482210321473860540420, 475368975085586025561263726600, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B6880, (.leaf 0 [] 0)]
theorem treeEq6879 : B6879.tree = HexagonCover.NBand.M8500_8700.SplitData.node6879 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6880
  · rfl

def B6878 : Block := .branch 167 ![1268888540267514781771602329985, 928606145193809753134859778, 4873482210321473860540420, 475368975085586025561263726600, 1329552514338574299630590216301019152, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B6879, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6878 : B6878.tree = HexagonCover.NBand.M8500_8700.SplitData.node6878 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6879
  · rfl

def B6814 : Block := .branch 108 ![1268888540267514781771602329985, 928606145193809753134859778, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip6812_6815, B6878, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6814 : B6814.tree = HexagonCover.NBand.M8500_8700.SplitData.node6814 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6878
  · rfl
  · rfl

def B6892 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6892 : B6892.tree = HexagonCover.NBand.M8500_8700.SplitData.node6892 := by
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

def B6891 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6892, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6891 : B6891.tree = HexagonCover.NBand.M8500_8700.SplitData.node6891 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6892
  · rfl
  · rfl
  · rfl

def B6890 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 362715524816251709573568516, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6891]
theorem treeEq6890 : B6890.tree = HexagonCover.NBand.M8500_8700.SplitData.node6890 := by
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
  · exact treeEq6891

def B6813 : Block := .branch 88 ![1268888540267514781771602329985, 619121135372464684410078722, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 1010).pointIds 1010), B6814, B6890, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6813 : B6813.tree = HexagonCover.NBand.M8500_8700.SplitData.node6813 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6814
  · exact treeEq6890
  · rfl
  · rfl
  · rfl
  · rfl

def B6894 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6894 : B6894.tree = HexagonCover.NBand.M8500_8700.SplitData.node6894 := by
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

def B6893 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6894, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq6893 : B6893.tree = HexagonCover.NBand.M8500_8700.SplitData.node6893 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6894
  · rfl
  · rfl
  · rfl

def B6812 : Block := .branch 100 ![1237940039285380274899124609, 619121135372464684410078722, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B6813, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B6893]
theorem treeEq6812 : B6812.tree = HexagonCover.NBand.M8500_8700.SplitData.node6812 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6813
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6893

theorem accepted6812 : B6812.accepted = true := by decide +kernel
theorem checked6812 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6812 (maskNeeds ![1237940039285380274899124609, 619121135372464684410078722, 130601767450242908029982724, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6812]
  exact B6812.sound accepted6812
#print axioms checked6812

def Tip6773_6777 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6777 ![1269507510287157471909051892097, 151115729774546960516610, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] HexagonCover.NBand.M8500_8700.SplitTree.Run0094.checked6777
def B6800 : Block := .branch 169 ![618970019642690137449562497, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6800 : B6800.tree = HexagonCover.NBand.M8500_8700.SplitData.node6800 := by
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

def B6799 : Block := .branch 170 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6800, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6799 : B6799.tree = HexagonCover.NBand.M8500_8700.SplitData.node6799 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6800
  · rfl

def B6798 : Block := .branch 163 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B6799]
theorem treeEq6798 : B6798.tree = HexagonCover.NBand.M8500_8700.SplitData.node6798 := by
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
  · exact treeEq6799

def B6797 : Block := .branch 165 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B6798, (.leaf 0 [] 0)]
theorem treeEq6797 : B6797.tree = HexagonCover.NBand.M8500_8700.SplitData.node6797 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6798
  · rfl

def B6796 : Block := .branch 167 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B6797, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6796 : B6796.tree = HexagonCover.NBand.M8500_8700.SplitData.node6796 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6797
  · rfl

def B6776 : Block := .branch 108 ![1269507510287157471909051892097, 151115729774546960516610, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip6773_6777, B6796, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6776 : B6776.tree = HexagonCover.NBand.M8500_8700.SplitData.node6776 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6796
  · rfl
  · rfl

def B6803 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6803 : B6803.tree = HexagonCover.NBand.M8500_8700.SplitData.node6803 := by
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

def B6802 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6803, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6802 : B6802.tree = HexagonCover.NBand.M8500_8700.SplitData.node6802 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6803
  · rfl
  · rfl
  · rfl

def B6801 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 362715524816251709573568516, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6802]
theorem treeEq6801 : B6801.tree = HexagonCover.NBand.M8500_8700.SplitData.node6801 := by
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
  · exact treeEq6802

def B6775 : Block := .branch 88 ![1269507510287157471909051892097, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 1005).pointIds 1005), B6776, B6801, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6775 : B6775.tree = HexagonCover.NBand.M8500_8700.SplitData.node6775 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6776
  · exact treeEq6801
  · rfl
  · rfl
  · rfl
  · rfl

def B6805 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6805 : B6805.tree = HexagonCover.NBand.M8500_8700.SplitData.node6805 := by
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

def B6804 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6805, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq6804 : B6804.tree = HexagonCover.NBand.M8500_8700.SplitData.node6804 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6805
  · rfl
  · rfl
  · rfl

def B6774 : Block := .branch 100 ![1856910058928070412348686721, 151115729774546960516610, 53230514994906640848787460, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B6775, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B6804]
theorem treeEq6774 : B6774.tree = HexagonCover.NBand.M8500_8700.SplitData.node6774 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6775
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6804

def B6810 : Block := .branch 169 ![618970019642690137449562497, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq6810 : B6810.tree = HexagonCover.NBand.M8500_8700.SplitData.node6810 := by
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

def B6809 : Block := .branch 170 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6810, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq6809 : B6809.tree = HexagonCover.NBand.M8500_8700.SplitData.node6809 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6810
  · rfl

def B6808 : Block := .branch 163 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B6809]
theorem treeEq6808 : B6808.tree = HexagonCover.NBand.M8500_8700.SplitData.node6808 := by
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
  · exact treeEq6809

def B6807 : Block := .branch 165 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B6808, (.leaf 0 [] 0)]
theorem treeEq6807 : B6807.tree = HexagonCover.NBand.M8500_8700.SplitData.node6807 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6808
  · rfl

def B6806 : Block := .branch 167 ![1856910058928070412348686721, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B6807, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq6806 : B6806.tree = HexagonCover.NBand.M8500_8700.SplitData.node6806 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6807
  · rfl

def B6773 : Block := .branch 98 ![1856910058928070412348686721, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6774, B6806, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6773 : B6773.tree = HexagonCover.NBand.M8500_8700.SplitData.node6773 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6774
  · exact treeEq6806
  · rfl
  · rfl

theorem accepted6773 : B6773.accepted = true := by decide +kernel
theorem checked6773 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6773 (maskNeeds ![1856910058928070412348686721, 151115729774546960516610, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6773]
  exact B6773.sound accepted6773
#print axioms checked6773

def B6930 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143617556573449800917725503496, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1114).pointIds 1114), (.leaf 4 (Common.fact 1040).pointIds 1040), (.leaf 5 (Common.fact 1026).pointIds 1026), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq6930 : B6930.tree = HexagonCover.NBand.M8500_8700.SplitData.node6930 := by
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

def B6929 : Block := .branch 98 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826704906516392450543549702152, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6930, (.leaf 4 (Common.fact 1113).pointIds 1113), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6929 : B6929.tree = HexagonCover.NBand.M8500_8700.SplitData.node6929 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6930
  · rfl
  · rfl
  · rfl

def B6928 : Block := .branch 108 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826704906516392450543549702152, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B6929, (.leaf 4 (Common.fact 1112).pointIds 1112), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6928 : B6928.tree = HexagonCover.NBand.M8500_8700.SplitData.node6928 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6929
  · rfl
  · rfl
  · rfl

def B6927 : Block := .branch 119 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826704906516392450543549702152, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B6928, (.leaf 4 (Common.fact 1111).pointIds 1111), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq6927 : B6927.tree = HexagonCover.NBand.M8500_8700.SplitData.node6927 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6928
  · rfl
  · rfl
  · rfl

def B6926 : Block := .branch 129 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826704906516392450543549702152, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B6927, (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq6926 : B6926.tree = HexagonCover.NBand.M8500_8700.SplitData.node6926 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6927
  · rfl
  · rfl
  · rfl

def B6925 : Block := .branch 138 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310795710359147084785718320020794440412901171208, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B6926, (.leaf 4 (Common.fact 1109).pointIds 1109), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq6925 : B6925.tree = HexagonCover.NBand.M8500_8700.SplitData.node6925 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6926
  · rfl
  · rfl
  · rfl

def B6924 : Block := .branch 146 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B6925, (.leaf 4 (Common.fact 1108).pointIds 1108), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq6924 : B6924.tree = HexagonCover.NBand.M8500_8700.SplitData.node6924 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6925
  · rfl
  · rfl
  · rfl

def B6923 : Block := .branch 162 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 782).pointIds 782), B6924, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6923 : B6923.tree = HexagonCover.NBand.M8500_8700.SplitData.node6923 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6924
  · rfl
  · rfl

def B6922 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6923, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6922 : B6922.tree = HexagonCover.NBand.M8500_8700.SplitData.node6922 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6923
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6921 : Block := .branch 101 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6922, (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 1099).pointIds 1099), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 1102).pointIds 1102), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq6921 : B6921.tree = HexagonCover.NBand.M8500_8700.SplitData.node6921 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6922
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6920 : Block := .branch 114 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6921, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq6920 : B6920.tree = HexagonCover.NBand.M8500_8700.SplitData.node6920 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6921
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6919 : Block := .branch 88 ![748288838313422294120287872290776191444112361128321, 618970019644942487019062786, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1096).pointIds 1096), B6920, (.leaf 2 (Common.fact 1097).pointIds 1097), (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6919 : B6919.tree = HexagonCover.NBand.M8500_8700.SplitData.node6919 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6920
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6918 : Block := .branch 160 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962293152177147703846966877249544, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6919, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6918 : B6918.tree = HexagonCover.NBand.M8500_8700.SplitData.node6918 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6919
  · rfl
  · rfl
  · rfl
  · rfl

def B6917 : Block := .branch 158 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962293152177147703846966877249544, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6918, (.leaf 5 (Common.fact 1012).pointIds 1012), (.leaf 0 [] 0)]
theorem treeEq6917 : B6917.tree = HexagonCover.NBand.M8500_8700.SplitData.node6917 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6918
  · rfl
  · rfl

def B6916 : Block := .branch 89 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310706507378352962293152177147703846966877249544, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1106).pointIds 1106), B6917, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6916 : B6916.tree = HexagonCover.NBand.M8500_8700.SplitData.node6916 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6917
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6915 : Block := .branch 172 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 77371252455336267181219848, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6916, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6915 : B6915.tree = HexagonCover.NBand.M8500_8700.SplitData.node6915 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6916
  · rfl
  · rfl
  · rfl

def B6914 : Block := .branch 159 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 77371252455336267181219848, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 1095).pointIds 1095), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6915]
theorem treeEq6914 : B6914.tree = HexagonCover.NBand.M8500_8700.SplitData.node6914 := by
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
  · exact treeEq6915

def B6913 : Block := .branch 169 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158533696280984011454269120520, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![B6914, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6913 : B6913.tree = HexagonCover.NBand.M8500_8700.SplitData.node6913 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6912 : Block := .branch 170 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6913, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6912 : B6912.tree = HexagonCover.NBand.M8500_8700.SplitData.node6912 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6913
  · rfl

def B6911 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6912]
theorem treeEq6911 : B6911.tree = HexagonCover.NBand.M8500_8700.SplitData.node6911 := by
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
  · exact treeEq6912

theorem accepted6911 : B6911.accepted = true := by decide +kernel
theorem checked6911 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6911 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6911]
  exact B6911.sound accepted6911
#print axioms checked6911

def B6950 : Block := .branch 174 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 5986310796058808290812143578870947222132784134905864, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 1093).pointIds 1093), (.leaf 1 (Common.fact 1066).pointIds 1066), (.leaf 2 (Common.fact 1028).pointIds 1028), (.leaf 3 (Common.fact 1115).pointIds 1115), (.leaf 4 (Common.fact 1040).pointIds 1040), (.leaf 5 (Common.fact 1026).pointIds 1026), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq6950 : B6950.tree = HexagonCover.NBand.M8500_8700.SplitData.node6950 := by
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

def B6949 : Block := .branch 98 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826666220890164782409959104520, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B6950, (.leaf 4 (Common.fact 1113).pointIds 1113), (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq6949 : B6949.tree = HexagonCover.NBand.M8500_8700.SplitData.node6949 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6950
  · rfl
  · rfl
  · rfl

def B6948 : Block := .branch 108 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826666220890164782409959104520, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), B6949, (.leaf 4 (Common.fact 1112).pointIds 1112), (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq6948 : B6948.tree = HexagonCover.NBand.M8500_8700.SplitData.node6948 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6949
  · rfl
  · rfl
  · rfl

def B6947 : Block := .branch 119 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826666220890164782409959104520, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B6948, (.leaf 4 (Common.fact 1111).pointIds 1111), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq6947 : B6947.tree = HexagonCover.NBand.M8500_8700.SplitData.node6947 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6948
  · rfl
  · rfl
  · rfl

def B6946 : Block := .branch 129 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310796058808290811826666220890164782409959104520, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B6947, (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq6946 : B6946.tree = HexagonCover.NBand.M8500_8700.SplitData.node6946 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6947
  · rfl
  · rfl
  · rfl

def B6945 : Block := .branch 138 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310795710359147084785679634394566772279310573576, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B6946, (.leaf 4 (Common.fact 1109).pointIds 1109), (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq6945 : B6945.tree = HexagonCover.NBand.M8500_8700.SplitData.node6945 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6946
  · rfl
  · rfl
  · rfl

def B6944 : Block := .branch 146 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962293113491521476178833286651912, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), B6945, (.leaf 4 (Common.fact 1108).pointIds 1108), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq6944 : B6944.tree = HexagonCover.NBand.M8500_8700.SplitData.node6944 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6945
  · rfl
  · rfl
  · rfl

def B6943 : Block := .branch 162 ![748288838313422294121554284950965135465334165209473, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), (.leaf 3 (Common.fact 798).pointIds 798), B6944, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq6943 : B6943.tree = HexagonCover.NBand.M8500_8700.SplitData.node6943 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6944
  · rfl
  · rfl

def B6942 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6943, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq6942 : B6942.tree = HexagonCover.NBand.M8500_8700.SplitData.node6942 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6943
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6941 : Block := .branch 101 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6942, (.leaf 1 (Common.fact 1098).pointIds 1098), (.leaf 2 (Common.fact 1099).pointIds 1099), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 1101).pointIds 1101), (.leaf 5 (Common.fact 1102).pointIds 1102), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq6941 : B6941.tree = HexagonCover.NBand.M8500_8700.SplitData.node6941 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6942
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6940 : Block := .branch 114 ![748288838313422294120286634350736906063837462004097, 928455029466287555743843842, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![B6941, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq6940 : B6940.tree = HexagonCover.NBand.M8500_8700.SplitData.node6940 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6941
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6939 : Block := .branch 88 ![748288838313422294120287872290776191444112361128321, 618970019644942487019062786, 1461501637330902918203689668438008222246340925444, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1096).pointIds 1096), B6940, (.leaf 2 (Common.fact 1097).pointIds 1097), (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq6939 : B6939.tree = HexagonCover.NBand.M8500_8700.SplitData.node6939 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6940
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6938 : Block := .branch 160 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962451569816550004854020374552584, 365375409332725729550921208179070754913983234064, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6939, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6938 : B6938.tree = HexagonCover.NBand.M8500_8700.SplitData.node6938 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6939
  · rfl
  · rfl
  · rfl
  · rfl

def B6937 : Block := .branch 158 ![748288838313422294120287872290776191444112361128321, 619121135372464684410078722, 4835721725202590408382468, 5986310706507378352962451569816550004854020374552584, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B6938, (.leaf 5 (Common.fact 1012).pointIds 1012), (.leaf 0 [] 0)]
theorem treeEq6937 : B6937.tree = HexagonCover.NBand.M8500_8700.SplitData.node6937 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6938
  · rfl
  · rfl

def B6936 : Block := .branch 89 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4835721725202590408382468, 5986310706507378352962451569816550004854020374552584, 98320, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 1106).pointIds 1106), B6937, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq6936 : B6936.tree = HexagonCover.NBand.M8500_8700.SplitData.node6936 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6937
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6935 : Block := .branch 172 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115298993012691715283710893735980553372958784] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 868).pointIds 868), B6936, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6935 : B6935.tree = HexagonCover.NBand.M8500_8700.SplitData.node6935 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6936
  · rfl
  · rfl
  · rfl

def B6934 : Block := .branch 159 ![748288838313422294120287872290776191444112361128321, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 1095).pointIds 1095), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B6935]
theorem treeEq6934 : B6934.tree = HexagonCover.NBand.M8500_8700.SplitData.node6934 := by
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
  · exact treeEq6935

def B6933 : Block := .branch 169 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364480327561232613441294535594470725406687296] ![B6934, (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6933 : B6933.tree = HexagonCover.NBand.M8500_8700.SplitData.node6933 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6934
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6932 : Block := .branch 170 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 2993155364480327561232613441294535594470725406687296] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6933, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6932 : B6932.tree = HexagonCover.NBand.M8500_8700.SplitData.node6932 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6933
  · rfl

def B6931 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6932]
theorem treeEq6931 : B6931.tree = HexagonCover.NBand.M8500_8700.SplitData.node6931 := by
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
  · exact treeEq6932

theorem accepted6931 : B6931.accepted = true := by decide +kernel
theorem checked6931 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node6931 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq6931]
  exact B6931.sound accepted6931
#print axioms checked6931

end HexagonCover.NBand.M8500_8700.SplitTree.Run0096
