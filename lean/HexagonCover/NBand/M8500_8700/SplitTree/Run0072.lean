import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0071
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0072
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip5158_5195 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5195 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] HexagonCover.NBand.M8500_8700.SplitTree.Run0071.checked5195
def Tip5158_5159 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5159 ![5192298715444887133061660981330305, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0071.checked5159
def B5214 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq5214 : B5214.tree = HexagonCover.NBand.M8500_8700.SplitData.node5214 := by
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

def B5213 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5214, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq5213 : B5213.tree = HexagonCover.NBand.M8500_8700.SplitData.node5213 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5214
  · rfl

def B5212 : Block := .branch 163 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B5213]
theorem treeEq5212 : B5212.tree = HexagonCover.NBand.M8500_8700.SplitData.node5212 := by
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
  · exact treeEq5213

def B5211 : Block := .branch 165 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B5212, (.leaf 0 [] 0)]
theorem treeEq5211 : B5211.tree = HexagonCover.NBand.M8500_8700.SplitData.node5211 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5212
  · rfl

def B5210 : Block := .branch 167 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B5211, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq5210 : B5210.tree = HexagonCover.NBand.M8500_8700.SplitData.node5210 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5211
  · rfl

def B5194 : Block := .branch 119 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip5158_5195, B5210, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq5194 : B5194.tree = HexagonCover.NBand.M8500_8700.SplitData.node5194 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5210
  · rfl
  · rfl

def B5217 : Block := .branch 160 ![385, 151115729774546960516610, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq5217 : B5217.tree = HexagonCover.NBand.M8500_8700.SplitData.node5217 := by
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

def B5216 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), B5217, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq5216 : B5216.tree = HexagonCover.NBand.M8500_8700.SplitData.node5216 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5217
  · rfl
  · rfl
  · rfl
  · rfl

def B5215 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636754947642946489600292064235422744640] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), B5216, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq5215 : B5215.tree = HexagonCover.NBand.M8500_8700.SplitData.node5215 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5216
  · rfl
  · rfl
  · rfl

def B5193 : Block := .branch 114 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![B5194, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B5215]
theorem treeEq5193 : B5193.tree = HexagonCover.NBand.M8500_8700.SplitData.node5193 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5194
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5215

def B5192 : Block := .branch 159 ![10385863224579942990993654013755777, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 976).pointIds 976), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5193]
theorem treeEq5192 : B5192.tree = HexagonCover.NBand.M8500_8700.SplitData.node5192 := by
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
  · exact treeEq5193

def B5222 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq5222 : B5222.tree = HexagonCover.NBand.M8500_8700.SplitData.node5222 := by
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

def B5221 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5222, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq5221 : B5221.tree = HexagonCover.NBand.M8500_8700.SplitData.node5221 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5222
  · rfl

def B5220 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5221]
theorem treeEq5220 : B5220.tree = HexagonCover.NBand.M8500_8700.SplitData.node5220 := by
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
  · exact treeEq5221

def B5219 : Block := .branch 172 ![1237940039861841027202548097, 151115729774546960516610, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 851).pointIds 851), B5220, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq5219 : B5219.tree = HexagonCover.NBand.M8500_8700.SplitData.node5219 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5220
  · rfl
  · rfl
  · rfl

def B5218 : Block := .branch 160 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B5219, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq5218 : B5218.tree = HexagonCover.NBand.M8500_8700.SplitData.node5218 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5219
  · rfl
  · rfl
  · rfl
  · rfl

def B5191 : Block := .branch 113 ![1269507510287733932661355315585, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![B5192, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B5218]
theorem treeEq5191 : B5191.tree = HexagonCover.NBand.M8500_8700.SplitData.node5191 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5192
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5218

def B5158 : Block := .branch 112 ![1269507510287733932661355315585, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip5158_5159, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B5191]
theorem treeEq5158 : B5158.tree = HexagonCover.NBand.M8500_8700.SplitData.node5158 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5191

theorem accepted5158 : B5158.accepted = true := by decide +kernel
theorem checked5158 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5158 (maskNeeds ![1269507510287733932661355315585, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq5158]
  exact B5158.sound accepted5158
#print axioms checked5158

def B5251 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq5251 : B5251.tree = HexagonCover.NBand.M8500_8700.SplitData.node5251 := by
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

def B5250 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5251, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq5250 : B5250.tree = HexagonCover.NBand.M8500_8700.SplitData.node5250 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5251
  · rfl

def B5249 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5250]
theorem treeEq5249 : B5249.tree = HexagonCover.NBand.M8500_8700.SplitData.node5249 := by
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
  · exact treeEq5250

def B5256 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq5256 : B5256.tree = HexagonCover.NBand.M8500_8700.SplitData.node5256 := by
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

def B5255 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5256, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq5255 : B5255.tree = HexagonCover.NBand.M8500_8700.SplitData.node5255 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5256
  · rfl

def B5254 : Block := .branch 163 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B5255]
theorem treeEq5254 : B5254.tree = HexagonCover.NBand.M8500_8700.SplitData.node5254 := by
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
  · exact treeEq5255

def B5253 : Block := .branch 165 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B5254, (.leaf 0 [] 0)]
theorem treeEq5253 : B5253.tree = HexagonCover.NBand.M8500_8700.SplitData.node5253 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5254
  · rfl

def B5252 : Block := .branch 167 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B5253, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq5252 : B5252.tree = HexagonCover.NBand.M8500_8700.SplitData.node5252 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5253
  · rfl

def B5248 : Block := .branch 129 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B5249, B5252, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq5248 : B5248.tree = HexagonCover.NBand.M8500_8700.SplitData.node5248 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5249
  · exact treeEq5252
  · rfl
  · rfl

def B5261 : Block := .branch 160 ![385, 151115729774546960516610, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq5261 : B5261.tree = HexagonCover.NBand.M8500_8700.SplitData.node5261 := by
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

def B5260 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), B5261, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq5260 : B5260.tree = HexagonCover.NBand.M8500_8700.SplitData.node5260 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5261
  · rfl
  · rfl
  · rfl
  · rfl

def B5259 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), B5260, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq5259 : B5259.tree = HexagonCover.NBand.M8500_8700.SplitData.node5259 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5260
  · rfl
  · rfl
  · rfl

def B5258 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B5259]
theorem treeEq5258 : B5258.tree = HexagonCover.NBand.M8500_8700.SplitData.node5258 := by
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
  · exact treeEq5259

def B5257 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5258, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq5257 : B5257.tree = HexagonCover.NBand.M8500_8700.SplitData.node5257 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5258
  · rfl

def B5247 : Block := .branch 121 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B5248, (.leaf 5 (Common.fact 319).pointIds 319), B5257]
theorem treeEq5247 : B5247.tree = HexagonCover.NBand.M8500_8700.SplitData.node5247 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5248
  · rfl
  · exact treeEq5257

theorem accepted5247 : B5247.accepted = true := by decide +kernel
theorem checked5247 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5247 (maskNeeds ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq5247]
  exact B5247.sound accepted5247
#print axioms checked5247

def B5283 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq5283 : B5283.tree = HexagonCover.NBand.M8500_8700.SplitData.node5283 := by
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

def B5282 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5283, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq5282 : B5282.tree = HexagonCover.NBand.M8500_8700.SplitData.node5282 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5283
  · rfl

def B5281 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5282]
theorem treeEq5281 : B5281.tree = HexagonCover.NBand.M8500_8700.SplitData.node5281 := by
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
  · exact treeEq5282

def B5288 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq5288 : B5288.tree = HexagonCover.NBand.M8500_8700.SplitData.node5288 := by
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

def B5287 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5288, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq5287 : B5287.tree = HexagonCover.NBand.M8500_8700.SplitData.node5287 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5288
  · rfl

def B5286 : Block := .branch 163 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B5287]
theorem treeEq5286 : B5286.tree = HexagonCover.NBand.M8500_8700.SplitData.node5286 := by
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
  · exact treeEq5287

def B5285 : Block := .branch 165 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B5286, (.leaf 0 [] 0)]
theorem treeEq5285 : B5285.tree = HexagonCover.NBand.M8500_8700.SplitData.node5285 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5286
  · rfl

def B5284 : Block := .branch 167 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B5285, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq5284 : B5284.tree = HexagonCover.NBand.M8500_8700.SplitData.node5284 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5285
  · rfl

def B5280 : Block := .branch 129 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B5281, B5284, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq5280 : B5280.tree = HexagonCover.NBand.M8500_8700.SplitData.node5280 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5281
  · exact treeEq5284
  · rfl
  · rfl

def B5293 : Block := .branch 160 ![385, 151115729774546960516610, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq5293 : B5293.tree = HexagonCover.NBand.M8500_8700.SplitData.node5293 := by
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

def B5292 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), B5293, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq5292 : B5292.tree = HexagonCover.NBand.M8500_8700.SplitData.node5292 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5293
  · rfl
  · rfl
  · rfl
  · rfl

def B5291 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), B5292, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq5291 : B5291.tree = HexagonCover.NBand.M8500_8700.SplitData.node5291 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5292
  · rfl
  · rfl
  · rfl

def B5290 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B5291]
theorem treeEq5290 : B5290.tree = HexagonCover.NBand.M8500_8700.SplitData.node5290 := by
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
  · exact treeEq5291

def B5289 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5290, (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq5289 : B5289.tree = HexagonCover.NBand.M8500_8700.SplitData.node5289 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5290
  · rfl

def B5279 : Block := .branch 121 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B5280, (.leaf 5 (Common.fact 319).pointIds 319), B5289]
theorem treeEq5279 : B5279.tree = HexagonCover.NBand.M8500_8700.SplitData.node5279 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5280
  · rfl
  · exact treeEq5289

theorem accepted5279 : B5279.accepted = true := by decide +kernel
theorem checked5279 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5279 (maskNeeds ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032]) := by
  rw [← treeEq5279]
  exact B5279.sound accepted5279
#print axioms checked5279

def Tip5243_5247 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node5247 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] checked5247
def B5266 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq5266 : B5266.tree = HexagonCover.NBand.M8500_8700.SplitData.node5266 := by
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

def B5265 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5266, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq5265 : B5265.tree = HexagonCover.NBand.M8500_8700.SplitData.node5265 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5266
  · rfl

def B5264 : Block := .branch 163 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B5265]
theorem treeEq5264 : B5264.tree = HexagonCover.NBand.M8500_8700.SplitData.node5264 := by
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
  · exact treeEq5265

def B5263 : Block := .branch 165 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B5264, (.leaf 0 [] 0)]
theorem treeEq5263 : B5263.tree = HexagonCover.NBand.M8500_8700.SplitData.node5263 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5264
  · rfl

def B5262 : Block := .branch 167 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1994491030784690662809276902461767696, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B5263, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq5262 : B5262.tree = HexagonCover.NBand.M8500_8700.SplitData.node5262 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5263
  · rfl

def B5246 : Block := .branch 119 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), Tip5243_5247, B5262, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq5246 : B5246.tree = HexagonCover.NBand.M8500_8700.SplitData.node5246 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5262
  · rfl
  · rfl

def B5269 : Block := .branch 160 ![385, 151115729774546960516610, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq5269 : B5269.tree = HexagonCover.NBand.M8500_8700.SplitData.node5269 := by
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

def B5268 : Block := .branch 172 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), B5269, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq5268 : B5268.tree = HexagonCover.NBand.M8500_8700.SplitData.node5268 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5269
  · rfl
  · rfl
  · rfl
  · rfl

def B5267 : Block := .branch 171 ![1237940039285380274899124609, 151115729774546960516610, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 730762012636749755346087954772663533739093524544] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), B5268, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq5267 : B5267.tree = HexagonCover.NBand.M8500_8700.SplitData.node5267 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5268
  · rfl
  · rfl
  · rfl

def B5245 : Block := .branch 114 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B5246, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B5267]
theorem treeEq5245 : B5245.tree = HexagonCover.NBand.M8500_8700.SplitData.node5245 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5246
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5267

def B5274 : Block := .branch 169 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 974).pointIds 974), (.leaf 1 (Common.fact 975).pointIds 975), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq5274 : B5274.tree = HexagonCover.NBand.M8500_8700.SplitData.node5274 := by
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

def B5273 : Block := .branch 170 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 972).pointIds 972), (.leaf 1 (Common.fact 973).pointIds 973), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B5274, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq5273 : B5273.tree = HexagonCover.NBand.M8500_8700.SplitData.node5273 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5274
  · rfl

def B5272 : Block := .branch 171 ![1237940039861841027202548097, 151115729774546960516610, 37778931862957161715716, 5986310706507378353287287002275110839777933679157256, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 970).pointIds 970), (.leaf 1 (Common.fact 971).pointIds 971), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 852).pointIds 852), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B5273]
theorem treeEq5272 : B5272.tree = HexagonCover.NBand.M8500_8700.SplitData.node5272 := by
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
  · exact treeEq5273

def B5271 : Block := .branch 172 ![1237940039861841027202548097, 151115729774546960516610, 1461501637330902918203694541901771799646491908100, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 968).pointIds 968), (.leaf 1 (Common.fact 969).pointIds 969), (.leaf 2 (Common.fact 851).pointIds 851), B5272, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq5271 : B5271.tree = HexagonCover.NBand.M8500_8700.SplitData.node5271 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5272
  · rfl
  · rfl
  · rfl

def B5270 : Block := .branch 160 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329227995784915872903807060280442896, 393248, 730762012636739370752370885117406472746435084352] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 981).pointIds 981), B5271, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq5270 : B5270.tree = HexagonCover.NBand.M8500_8700.SplitData.node5270 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5271
  · rfl
  · rfl
  · rfl
  · rfl

def B5244 : Block := .branch 113 ![1237940039861841027202548097, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![B5245, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B5270]
theorem treeEq5244 : B5244.tree = HexagonCover.NBand.M8500_8700.SplitData.node5244 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq5245
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5270

def B5243 : Block := .branch 159 ![5193565747075390867678199587799425, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 982).pointIds 982), (.leaf 1 (Common.fact 967).pointIds 967), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B5244]
theorem treeEq5243 : B5243.tree = HexagonCover.NBand.M8500_8700.SplitData.node5243 := by
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
  · exact treeEq5244

theorem accepted5243 : B5243.accepted = true := by decide +kernel
theorem checked5243 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node5243 (maskNeeds ![5193565747075390867678199587799425, 151115729774546960516610, 9709185488779990559365124, 324993927469215591267233983127560, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq5243]
  exact B5243.sound accepted5243
#print axioms checked5243

end HexagonCover.NBand.M8500_8700.SplitTree.Run0072
