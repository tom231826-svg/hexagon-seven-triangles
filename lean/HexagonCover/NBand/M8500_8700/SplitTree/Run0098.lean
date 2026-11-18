import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0058
import HexagonCover.NBand.M8500_8700.SplitTree.Run0066
import HexagonCover.NBand.M8500_8700.SplitTree.Run0074
import HexagonCover.NBand.M8500_8700.SplitTree.Run0082
import HexagonCover.NBand.M8500_8700.SplitTree.Run0090
import HexagonCover.NBand.M8500_8700.SplitTree.Run0097
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0098
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip5905_6289 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6289 ![1237940334433285454251950465, 151115729774546960516610, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0090.checked6289
def Tip5905_6193 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6193 ![1237940334433285454251950465, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0090.checked6193
def Tip5905_5907 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5907 ![1238242565888189111545627009, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0090.checked5907
def B6470 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6470 : B6470.tree = HexagonCover.NBand.M8500_8700.SplitData.node6470 := by
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

def B6469 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6470, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6469 : B6469.tree = HexagonCover.NBand.M8500_8700.SplitData.node6469 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6470
  · rfl

def B6468 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6469]
theorem treeEq6468 : B6468.tree = HexagonCover.NBand.M8500_8700.SplitData.node6468 := by
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
  · exact treeEq6469

def B6288 : Block := .branch 85 ![1237940334433285454251950465, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), Tip5905_6289, B6468, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq6288 : B6288.tree = HexagonCover.NBand.M8500_8700.SplitData.node6288 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6468
  · rfl
  · rfl
  · rfl

def B6473 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6473 : B6473.tree = HexagonCover.NBand.M8500_8700.SplitData.node6473 := by
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

def B6472 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6473, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6472 : B6472.tree = HexagonCover.NBand.M8500_8700.SplitData.node6472 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6473
  · rfl

def B6471 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6472]
theorem treeEq6471 : B6471.tree = HexagonCover.NBand.M8500_8700.SplitData.node6471 := by
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
  · exact treeEq6472

def B6287 : Block := .branch 84 ![1237940334433285454251950465, 151115729774546960516610, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B6288, B6471, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq6287 : B6287.tree = HexagonCover.NBand.M8500_8700.SplitData.node6287 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6288
  · exact treeEq6471
  · rfl
  · rfl
  · rfl

def B6476 : Block := .branch 169 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 988).pointIds 988), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq6476 : B6476.tree = HexagonCover.NBand.M8500_8700.SplitData.node6476 := by
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

def B6475 : Block := .branch 170 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B6476, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq6475 : B6475.tree = HexagonCover.NBand.M8500_8700.SplitData.node6475 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6476
  · rfl

def B6474 : Block := .branch 171 ![1237940334433285454251950465, 151115729774546960516610, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6475]
theorem treeEq6474 : B6474.tree = HexagonCover.NBand.M8500_8700.SplitData.node6474 := by
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
  · exact treeEq6475

def B6286 : Block := .branch 83 ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B6287, B6474, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq6286 : B6286.tree = HexagonCover.NBand.M8500_8700.SplitData.node6286 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6287
  · exact treeEq6474
  · rfl
  · rfl
  · rfl

def B6192 : Block := .branch 82 ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), Tip5905_6193, B6286, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq6192 : B6192.tree = HexagonCover.NBand.M8500_8700.SplitData.node6192 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6286
  · rfl
  · rfl
  · rfl

def B5906 : Block := .branch 78 ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![Tip5905_5907, B6192, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq5906 : B5906.tree = HexagonCover.NBand.M8500_8700.SplitData.node5906 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6192
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6479 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6479 : B6479.tree = HexagonCover.NBand.M8500_8700.SplitData.node6479 := by
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

def B6478 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 889).pointIds 889), B6479, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6478 : B6478.tree = HexagonCover.NBand.M8500_8700.SplitData.node6478 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6479
  · rfl
  · rfl
  · rfl

def B6477 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6478]
theorem treeEq6477 : B6477.tree = HexagonCover.NBand.M8500_8700.SplitData.node6477 := by
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
  · exact treeEq6478

def B5905 : Block := .branch 76 ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), B5906, B6477, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq5905 : B5905.tree = HexagonCover.NBand.M8500_8700.SplitData.node5905 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5906
  · exact treeEq6477
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5905 : B5905.accepted = true := by decide +kernel
theorem checked5905 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5905 (maskNeeds ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq5905]
  exact B5905.sound accepted5905
#print axioms checked5905

def Tip5903_6770 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6770 ![1237940039285380274899124609, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0097.checked6770
def Tip5903_6951 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6951 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0097.checked6951
def Tip5903_6971 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6971 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0097.checked6971
def Tip5903_6482 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node6482 ![1238242270740283932192801153, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0097.checked6482
def Tip5903_5905 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5905 ![1237940334433285454251950465, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] checked5905
def B6769 : Block := .branch 84 ![1237940039285380274899124609, 151115729774546960516610, 14544907213982580967741444, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip5903_6770, Tip5903_6951, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq6769 : B6769.tree = HexagonCover.NBand.M8500_8700.SplitData.node6769 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6768 : Block := .branch 83 ![1237940039285380274899124609, 151115729774546960516610, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B6769, Tip5903_6971, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq6768 : B6768.tree = HexagonCover.NBand.M8500_8700.SplitData.node6768 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6769
  · rfl
  · rfl
  · rfl
  · rfl

def B6996 : Block := .branch 100 ![23945242826029513411849172299223580994042798784119169, 1538, 6148, 24584, 98320, 393248, 14965776766312044560667477927645982992854494297456704] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 1132).pointIds 1132)]
theorem treeEq6996 : B6996.tree = HexagonCover.NBand.M8500_8700.SplitData.node6996 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6995 : Block := .branch 174 ![385, 377789320881921186596354, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 14965776766312044560667477927645982992854494297456704] ![B6996, (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1129).pointIds 1129), (.leaf 4 (Common.fact 1130).pointIds 1130), (.leaf 5 (Common.fact 1080).pointIds 1080), (.leaf 6 (Common.fact 1131).pointIds 1131)]
theorem treeEq6995 : B6995.tree = HexagonCover.NBand.M8500_8700.SplitData.node6995 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq6996
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6994 : Block := .branch 171 ![1237940039285380274899124609, 528905048404118577612290, 37778931862957161715716, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B6995]
theorem treeEq6994 : B6994.tree = HexagonCover.NBand.M8500_8700.SplitData.node6994 := by
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
  · exact treeEq6995

def B6993 : Block := .branch 172 ![1237940039285380274899124609, 528905048404118577612290, 1461501637330902918203684870495214882613094258692, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 1125).pointIds 1125), B6994, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq6993 : B6993.tree = HexagonCover.NBand.M8500_8700.SplitData.node6993 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6994
  · rfl
  · rfl
  · rfl

def B6992 : Block := .branch 160 ![1237940039285380274899124609, 528905048404118577612290, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11972621413058355384186331390243035368599144449441856] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B6993, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 1124).pointIds 1124)]
theorem treeEq6992 : B6992.tree = HexagonCover.NBand.M8500_8700.SplitData.node6992 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6993
  · rfl
  · rfl
  · rfl
  · rfl

def B6991 : Block := .branch 173 ![1237940039285380274899124609, 528905048404118577612290, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 43598678261745240631244871577745057382464] ![(.leaf 0 (Common.fact 1119).pointIds 1119), (.leaf 1 (Common.fact 1120).pointIds 1120), (.leaf 2 (Common.fact 1121).pointIds 1121), (.leaf 3 (Common.fact 1122).pointIds 1122), (.leaf 4 (Common.fact 1123).pointIds 1123), (.leaf 5 (Common.fact 1074).pointIds 1074), B6992]
theorem treeEq6991 : B6991.tree = HexagonCover.NBand.M8500_8700.SplitData.node6991 := by
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
  · exact treeEq6992

def B6767 : Block := .branch 82 ![1237940039285380274899124609, 528905048404118577612290, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B6768, B6991, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq6767 : B6767.tree = HexagonCover.NBand.M8500_8700.SplitData.node6767 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6768
  · exact treeEq6991
  · rfl
  · rfl
  · rfl

def B6481 : Block := .branch 78 ![1237940039285380274899124609, 226673593500461283935746, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![Tip5903_6482, B6767, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq6481 : B6481.tree = HexagonCover.NBand.M8500_8700.SplitData.node6481 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6767
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6999 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq6999 : B6999.tree = HexagonCover.NBand.M8500_8700.SplitData.node6999 := by
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

def B6998 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 889).pointIds 889), B6999, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq6998 : B6998.tree = HexagonCover.NBand.M8500_8700.SplitData.node6998 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6999
  · rfl
  · rfl
  · rfl

def B6997 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B6998]
theorem treeEq6997 : B6997.tree = HexagonCover.NBand.M8500_8700.SplitData.node6997 := by
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
  · exact treeEq6998

def B6480 : Block := .branch 76 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), B6481, B6997, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq6480 : B6480.tree = HexagonCover.NBand.M8500_8700.SplitData.node6480 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6481
  · exact treeEq6997
  · rfl
  · rfl
  · rfl
  · rfl

def B5904 : Block := .branch 68 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![Tip5903_5905, B6480, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq5904 : B5904.tree = HexagonCover.NBand.M8500_8700.SplitData.node5904 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6480
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7002 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq7002 : B7002.tree = HexagonCover.NBand.M8500_8700.SplitData.node7002 := by
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

def B7001 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 917).pointIds 917), B7002, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq7001 : B7001.tree = HexagonCover.NBand.M8500_8700.SplitData.node7001 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7002
  · rfl
  · rfl
  · rfl

def B7000 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B7001]
theorem treeEq7000 : B7000.tree = HexagonCover.NBand.M8500_8700.SplitData.node7000 := by
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
  · exact treeEq7001

def B5903 : Block := .branch 65 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 221).pointIds 221), B5904, B7000, (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 225).pointIds 225)]
theorem treeEq5903 : B5903.tree = HexagonCover.NBand.M8500_8700.SplitData.node5903 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5904
  · exact treeEq7000
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5903 : B5903.accepted = true := by decide +kernel
theorem checked5903 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5903 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq5903]
  exact B5903.sound accepted5903
#print axioms checked5903

def Tip4774_4779 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4779 ![1237940335009746206555373953, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0074.checked4779
def Tip4774_5340 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5340 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0082.checked5340
def Tip4774_5903 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5903 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] checked5903
def B5338 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq5338 : B5338.tree = HexagonCover.NBand.M8500_8700.SplitData.node5338 := by
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

def B5337 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 889).pointIds 889), B5338, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq5337 : B5337.tree = HexagonCover.NBand.M8500_8700.SplitData.node5337 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5338
  · rfl
  · rfl
  · rfl

def B5336 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B5337]
theorem treeEq5336 : B5336.tree = HexagonCover.NBand.M8500_8700.SplitData.node5336 := by
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
  · exact treeEq5337

def B4778 : Block := .branch 76 ![1237940335009746206555373953, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), Tip4774_4779, B5336, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq4778 : B4778.tree = HexagonCover.NBand.M8500_8700.SplitData.node4778 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5336
  · rfl
  · rfl
  · rfl
  · rfl

def B5899 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq5899 : B5899.tree = HexagonCover.NBand.M8500_8700.SplitData.node5899 := by
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

def B5898 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 889).pointIds 889), B5899, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq5898 : B5898.tree = HexagonCover.NBand.M8500_8700.SplitData.node5898 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5899
  · rfl
  · rfl
  · rfl

def B5897 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 113336795588871485134852, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B5898]
theorem treeEq5897 : B5897.tree = HexagonCover.NBand.M8500_8700.SplitData.node5897 := by
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
  · exact treeEq5898

def B5339 : Block := .branch 76 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), Tip4774_5340, B5897, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq5339 : B5339.tree = HexagonCover.NBand.M8500_8700.SplitData.node5339 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5897
  · rfl
  · rfl
  · rfl
  · rfl

def B4777 : Block := .branch 68 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![B4778, B5339, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq4777 : B4777.tree = HexagonCover.NBand.M8500_8700.SplitData.node4777 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq4778
  · exact treeEq5339
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5902 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq5902 : B5902.tree = HexagonCover.NBand.M8500_8700.SplitData.node5902 := by
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

def B5901 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 917).pointIds 917), B5902, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq5901 : B5901.tree = HexagonCover.NBand.M8500_8700.SplitData.node5901 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5902
  · rfl
  · rfl
  · rfl

def B5900 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 37815825351104580818948, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B5901]
theorem treeEq5900 : B5900.tree = HexagonCover.NBand.M8500_8700.SplitData.node5900 := by
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
  · exact treeEq5901

def B4776 : Block := .branch 65 ![1237940039861841027202548097, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 221).pointIds 221), B4777, B5900, (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 225).pointIds 225)]
theorem treeEq4776 : B4776.tree = HexagonCover.NBand.M8500_8700.SplitData.node4776 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4777
  · exact treeEq5900
  · rfl
  · rfl
  · rfl
  · rfl

def B4775 : Block := .branch 59 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![B4776, Tip4774_5903, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq4775 : B4775.tree = HexagonCover.NBand.M8500_8700.SplitData.node4775 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq4776
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7005 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq7005 : B7005.tree = HexagonCover.NBand.M8500_8700.SplitData.node7005 := by
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

def B7004 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 952).pointIds 952), B7005, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq7004 : B7004.tree = HexagonCover.NBand.M8500_8700.SplitData.node7004 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7005
  · rfl
  · rfl
  · rfl

def B7003 : Block := .branch 160 ![1237940039285380274899124609, 151115729774546960516610, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B7004]
theorem treeEq7003 : B7003.tree = HexagonCover.NBand.M8500_8700.SplitData.node7003 := by
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
  · exact treeEq7004

def B4774 : Block := .branch 55 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 211).pointIds 211), B4775, B7003, (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), (.leaf 6 (Common.fact 215).pointIds 215)]
theorem treeEq4774 : B4774.tree = HexagonCover.NBand.M8500_8700.SplitData.node4774 := by
  change Tree.branch (55 : Fin 175) _ = Tree.branch (55 : Fin 175) _
  apply congrArg (Tree.branch (55 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4775
  · exact treeEq7003
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4774 : B4774.accepted = true := by decide +kernel
theorem checked4774 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4774 (maskNeeds ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq4774]
  exact B4774.sound accepted4774
#print axioms checked4774

def Tip0035_3622 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3622 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0058.checked3622
def Tip0035_4197 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4197 ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0066.checked4197
def Tip0035_0037 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0037 ![1237940039287632074712809857, 151115763481175421617666, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] HexagonCover.NBand.M8500_8700.SplitTree.Run0066.checked0037
def Tip0035_4774 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4774 ![1237940039285380274899124609, 151115729774546960516610, 37797378607030871267332, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] checked4774
def B4195 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq4195 : B4195.tree = HexagonCover.NBand.M8500_8700.SplitData.node4195 := by
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

def B4194 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4195, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq4194 : B4194.tree = HexagonCover.NBand.M8500_8700.SplitData.node4194 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4195
  · rfl
  · rfl
  · rfl

def B4193 : Block := .branch 160 ![1237940039287632074712809857, 151447768916073918760450, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B4194]
theorem treeEq4193 : B4193.tree = HexagonCover.NBand.M8500_8700.SplitData.node4193 := by
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
  · exact treeEq4194

def B3621 : Block := .branch 68 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![Tip0035_3622, B4193, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq3621 : B3621.tree = HexagonCover.NBand.M8500_8700.SplitData.node3621 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4193
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4770 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq4770 : B4770.tree = HexagonCover.NBand.M8500_8700.SplitData.node4770 := by
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

def B4769 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4770, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq4769 : B4769.tree = HexagonCover.NBand.M8500_8700.SplitData.node4769 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4770
  · rfl
  · rfl
  · rfl

def B4768 : Block := .branch 160 ![1237940039287632074712809857, 151410875427926499657218, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 963).pointIds 963), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B4769]
theorem treeEq4768 : B4768.tree = HexagonCover.NBand.M8500_8700.SplitData.node4768 := by
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
  · exact treeEq4769

def B4196 : Block := .branch 68 ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![Tip0035_4197, B4768, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq4196 : B4196.tree = HexagonCover.NBand.M8500_8700.SplitData.node4196 := by
  change Tree.branch (68 : Fin 175) _ = Tree.branch (68 : Fin 175) _
  apply congrArg (Tree.branch (68 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3620 : Block := .branch 65 ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 221).pointIds 221), B3621, B4196, (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 225).pointIds 225)]
theorem treeEq3620 : B3620.tree = HexagonCover.NBand.M8500_8700.SplitData.node3620 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3621
  · exact treeEq4196
  · rfl
  · rfl
  · rfl
  · rfl

def B4773 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq4773 : B4773.tree = HexagonCover.NBand.M8500_8700.SplitData.node4773 := by
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

def B4772 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4773, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq4772 : B4772.tree = HexagonCover.NBand.M8500_8700.SplitData.node4772 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4773
  · rfl
  · rfl
  · rfl

def B4771 : Block := .branch 160 ![1237940039287632074712809857, 151116303983499450254850, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B4772]
theorem treeEq4771 : B4771.tree = HexagonCover.NBand.M8500_8700.SplitData.node4771 := by
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
  · exact treeEq4772

def B3619 : Block := .branch 59 ![1237940039287632074712809857, 151115727522747146831362, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B3620, B4771, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq3619 : B3619.tree = HexagonCover.NBand.M8500_8700.SplitData.node3619 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3620
  · exact treeEq4771
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0036 : Block := .branch 55 ![1237940039287632074712809857, 151115727522747146831362, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 211).pointIds 211), Tip0035_0037, B3619, (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), (.leaf 6 (Common.fact 215).pointIds 215)]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M8500_8700.SplitData.node0036 := by
  change Tree.branch (55 : Fin 175) _ = Tree.branch (55 : Fin 175) _
  apply congrArg (Tree.branch (55 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3619
  · rfl
  · rfl
  · rfl
  · rfl

def B0035 : Block := .branch 51 ![1237940039285380274899124609, 151115727522747146831362, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B0036, Tip0035_4774, (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), (.leaf 4 (Common.fact 209).pointIds 209), (.leaf 5 (Common.fact 210).pointIds 210), (.leaf 0 [] 0)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M8500_8700.SplitData.node0035 := by
  change Tree.branch (51 : Fin 175) _ = Tree.branch (51 : Fin 175) _
  apply congrArg (Tree.branch (51 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0036
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0035 : B0035.accepted = true := by decide +kernel
theorem checked0035 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0035 (maskNeeds ![1237940039285380274899124609, 151115727522747146831362, 37797378607030871267332, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq0035]
  exact B0035.sound accepted0035
#print axioms checked0035

end HexagonCover.NBand.M8500_8700.SplitTree.Run0098
