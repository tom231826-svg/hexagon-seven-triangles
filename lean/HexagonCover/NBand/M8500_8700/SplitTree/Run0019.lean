import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0018
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0019
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1365_1368 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1368 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] HexagonCover.NBand.M8500_8700.SplitTree.Run0018.checked1368
def B1391 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1391 : B1391.tree = HexagonCover.NBand.M8500_8700.SplitData.node1391 := by
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

def B1390 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1391, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1390 : B1390.tree = HexagonCover.NBand.M8500_8700.SplitData.node1390 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1391
  · rfl

def B1389 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1390]
theorem treeEq1389 : B1389.tree = HexagonCover.NBand.M8500_8700.SplitData.node1389 := by
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
  · exact treeEq1390

def B1388 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1389, (.leaf 0 [] 0)]
theorem treeEq1388 : B1388.tree = HexagonCover.NBand.M8500_8700.SplitData.node1388 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1389
  · rfl

def B1387 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1388, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1387 : B1387.tree = HexagonCover.NBand.M8500_8700.SplitData.node1387 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1388
  · rfl

def B1367 : Block := .branch 108 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip1365_1368, B1387, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1367 : B1367.tree = HexagonCover.NBand.M8500_8700.SplitData.node1367 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1387
  · rfl
  · rfl

def B1393 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1393 : B1393.tree = HexagonCover.NBand.M8500_8700.SplitData.node1393 := by
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

def B1392 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1393, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1392 : B1392.tree = HexagonCover.NBand.M8500_8700.SplitData.node1392 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1393
  · rfl
  · rfl
  · rfl

def B1366 : Block := .branch 100 ![1856910059506782964465795457, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B1367, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1392]
theorem treeEq1366 : B1366.tree = HexagonCover.NBand.M8500_8700.SplitData.node1366 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1392

def B1398 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1398 : B1398.tree = HexagonCover.NBand.M8500_8700.SplitData.node1398 := by
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

def B1397 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1398, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1397 : B1397.tree = HexagonCover.NBand.M8500_8700.SplitData.node1397 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1398
  · rfl

def B1396 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1397]
theorem treeEq1396 : B1396.tree = HexagonCover.NBand.M8500_8700.SplitData.node1396 := by
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
  · exact treeEq1397

def B1395 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1396, (.leaf 0 [] 0)]
theorem treeEq1395 : B1395.tree = HexagonCover.NBand.M8500_8700.SplitData.node1395 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1396
  · rfl

def B1394 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1395, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1394 : B1394.tree = HexagonCover.NBand.M8500_8700.SplitData.node1394 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1395
  · rfl

def B1365 : Block := .branch 98 ![1856910059506782964465795457, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1366, B1394, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1365 : B1365.tree = HexagonCover.NBand.M8500_8700.SplitData.node1365 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1366
  · exact treeEq1394
  · rfl
  · rfl

theorem accepted1365 : B1365.accepted = true := by decide +kernel
theorem checked1365 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1365 (maskNeeds ![1856910059506782964465795457, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1365]
  exact B1365.sound accepted1365
#print axioms checked1365

def Tip1363_1402 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1402 ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] HexagonCover.NBand.M8500_8700.SplitTree.Run0018.checked1402
def Tip1363_1365 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1365 ![1856910059506782964465795457, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] checked1365
def B1425 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1425 : B1425.tree = HexagonCover.NBand.M8500_8700.SplitData.node1425 := by
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

def B1424 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1425, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1424 : B1424.tree = HexagonCover.NBand.M8500_8700.SplitData.node1424 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1425
  · rfl

def B1423 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1424]
theorem treeEq1423 : B1423.tree = HexagonCover.NBand.M8500_8700.SplitData.node1423 := by
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
  · exact treeEq1424

def B1422 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1423, (.leaf 0 [] 0)]
theorem treeEq1422 : B1422.tree = HexagonCover.NBand.M8500_8700.SplitData.node1422 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1423
  · rfl

def B1421 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1422, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1421 : B1421.tree = HexagonCover.NBand.M8500_8700.SplitData.node1421 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1422
  · rfl

def B1401 : Block := .branch 108 ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip1363_1402, B1421, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1401 : B1401.tree = HexagonCover.NBand.M8500_8700.SplitData.node1401 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1421
  · rfl
  · rfl

def B1427 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1427 : B1427.tree = HexagonCover.NBand.M8500_8700.SplitData.node1427 := by
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

def B1426 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1427, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1426 : B1426.tree = HexagonCover.NBand.M8500_8700.SplitData.node1426 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1427
  · rfl
  · rfl
  · rfl

def B1400 : Block := .branch 100 ![1238242271318996484309909889, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B1401, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1426]
theorem treeEq1400 : B1400.tree = HexagonCover.NBand.M8500_8700.SplitData.node1400 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1401
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1426

def B1432 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1432 : B1432.tree = HexagonCover.NBand.M8500_8700.SplitData.node1432 := by
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

def B1431 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1432, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1431 : B1431.tree = HexagonCover.NBand.M8500_8700.SplitData.node1431 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1432
  · rfl

def B1430 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1431]
theorem treeEq1430 : B1430.tree = HexagonCover.NBand.M8500_8700.SplitData.node1430 := by
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
  · exact treeEq1431

def B1429 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1430, (.leaf 0 [] 0)]
theorem treeEq1429 : B1429.tree = HexagonCover.NBand.M8500_8700.SplitData.node1429 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1430
  · rfl

def B1428 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1429, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1428 : B1428.tree = HexagonCover.NBand.M8500_8700.SplitData.node1428 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1429
  · rfl

def B1399 : Block := .branch 98 ![1238242271318996484309909889, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1400, B1428, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1399 : B1399.tree = HexagonCover.NBand.M8500_8700.SplitData.node1399 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1400
  · exact treeEq1428
  · rfl
  · rfl

def B1364 : Block := .branch 89 ![1238242271318996484309909889, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![Tip1363_1365, B1399, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq1364 : B1364.tree = HexagonCover.NBand.M8500_8700.SplitData.node1364 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1399
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1435 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1435 : B1435.tree = HexagonCover.NBand.M8500_8700.SplitData.node1435 := by
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

def B1434 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1435, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq1434 : B1434.tree = HexagonCover.NBand.M8500_8700.SplitData.node1434 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1435
  · rfl
  · rfl
  · rfl

def B1433 : Block := .branch 160 ![1237940039864092827016233345, 151447768845705174582786, 362715524816251709573568516, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B1434]
theorem treeEq1433 : B1433.tree = HexagonCover.NBand.M8500_8700.SplitData.node1433 := by
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
  · exact treeEq1434

def B1363 : Block := .branch 88 ![1238242271318996484309909889, 151447768845705174582786, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), B1364, B1433, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq1363 : B1363.tree = HexagonCover.NBand.M8500_8700.SplitData.node1363 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1364
  · exact treeEq1433
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1363 : B1363.accepted = true := by decide +kernel
theorem checked1363 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1363 (maskNeeds ![1238242271318996484309909889, 151447768845705174582786, 53230533441650714558339076, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1363]
  exact B1363.sound accepted1363
#print axioms checked1363

def B1467 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1467 : B1467.tree = HexagonCover.NBand.M8500_8700.SplitData.node1467 := by
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

def B1466 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1467, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1466 : B1466.tree = HexagonCover.NBand.M8500_8700.SplitData.node1466 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1467
  · rfl

def B1465 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1466]
theorem treeEq1465 : B1465.tree = HexagonCover.NBand.M8500_8700.SplitData.node1465 := by
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
  · exact treeEq1466

def B1472 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1472 : B1472.tree = HexagonCover.NBand.M8500_8700.SplitData.node1472 := by
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

def B1471 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283952331788132477192413569001236987968] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1472, (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1471 : B1471.tree = HexagonCover.NBand.M8500_8700.SplitData.node1471 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1472
  · rfl

def B1470 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1471]
theorem treeEq1470 : B1470.tree = HexagonCover.NBand.M8500_8700.SplitData.node1470 := by
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
  · exact treeEq1471

def B1469 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1470, (.leaf 0 [] 0)]
theorem treeEq1469 : B1469.tree = HexagonCover.NBand.M8500_8700.SplitData.node1469 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1470
  · rfl

def B1468 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1469, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1468 : B1468.tree = HexagonCover.NBand.M8500_8700.SplitData.node1468 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1469
  · rfl

def B1464 : Block := .branch 129 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1465, B1468, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1464 : B1464.tree = HexagonCover.NBand.M8500_8700.SplitData.node1464 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1465
  · exact treeEq1468
  · rfl
  · rfl

def B1477 : Block := .branch 160 ![385, 151447768845705174582786, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1477 : B1477.tree = HexagonCover.NBand.M8500_8700.SplitData.node1477 := by
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

def B1476 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), B1477, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq1476 : B1476.tree = HexagonCover.NBand.M8500_8700.SplitData.node1476 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1477
  · rfl
  · rfl
  · rfl
  · rfl

def B1475 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061681562436857997944863089711799337024] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), B1476, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1475 : B1475.tree = HexagonCover.NBand.M8500_8700.SplitData.node1475 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1476
  · rfl
  · rfl
  · rfl

def B1474 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1475]
theorem treeEq1474 : B1474.tree = HexagonCover.NBand.M8500_8700.SplitData.node1474 := by
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
  · exact treeEq1475

def B1473 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639387442150223647207957025874337333312] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1474, (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1473 : B1473.tree = HexagonCover.NBand.M8500_8700.SplitData.node1473 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1474
  · rfl

def B1463 : Block := .branch 121 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B1464, (.leaf 5 (Common.fact 319).pointIds 319), B1473]
theorem treeEq1463 : B1463.tree = HexagonCover.NBand.M8500_8700.SplitData.node1463 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1464
  · rfl
  · exact treeEq1473

theorem accepted1463 : B1463.accepted = true := by decide +kernel
theorem checked1463 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1463 (maskNeeds ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303836210568746307946111725203524943936]) := by
  rw [← treeEq1463]
  exact B1463.sound accepted1463
#print axioms checked1463

def B1499 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1499 : B1499.tree = HexagonCover.NBand.M8500_8700.SplitData.node1499 := by
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

def B1498 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1499, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1498 : B1498.tree = HexagonCover.NBand.M8500_8700.SplitData.node1498 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1499
  · rfl

def B1497 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1498]
theorem treeEq1497 : B1497.tree = HexagonCover.NBand.M8500_8700.SplitData.node1497 := by
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
  · exact treeEq1498

def B1504 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq1504 : B1504.tree = HexagonCover.NBand.M8500_8700.SplitData.node1504 := by
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

def B1503 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 12422775111283957524084991012020042099497566208064] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1504, (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq1503 : B1503.tree = HexagonCover.NBand.M8500_8700.SplitData.node1503 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1504
  · rfl

def B1502 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B1503]
theorem treeEq1502 : B1502.tree = HexagonCover.NBand.M8500_8700.SplitData.node1502 := by
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
  · exact treeEq1503

def B1501 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B1502, (.leaf 0 [] 0)]
theorem treeEq1501 : B1501.tree = HexagonCover.NBand.M8500_8700.SplitData.node1501 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1502
  · rfl

def B1500 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B1501, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1500 : B1500.tree = HexagonCover.NBand.M8500_8700.SplitData.node1500 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1501
  · rfl

def B1496 : Block := .branch 129 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B1497, B1500, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq1496 : B1496.tree = HexagonCover.NBand.M8500_8700.SplitData.node1496 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1497
  · exact treeEq1500
  · rfl
  · rfl

def B1509 : Block := .branch 160 ![385, 151447768845705174582786, 5986310706507378352962293084515080737290690255394820, 24584, 98320, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq1509 : B1509.tree = HexagonCover.NBand.M8500_8700.SplitData.node1509 := by
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

def B1508 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), B1509, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1508 : B1508.tree = HexagonCover.NBand.M8500_8700.SplitData.node1508 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1509
  · rfl
  · rfl
  · rfl
  · rfl

def B1507 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 4835703278458516698849288, 1329227995784915872903807060280442896, 393248, 749019600326061686754733716532772491620208128557120] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), B1508, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1507 : B1507.tree = HexagonCover.NBand.M8500_8700.SplitData.node1507 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1508
  · rfl
  · rfl
  · rfl

def B1506 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B1507]
theorem treeEq1506 : B1506.tree = HexagonCover.NBand.M8500_8700.SplitData.node1506 := by
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
  · exact treeEq1507

def B1505 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 730762012639392634447082182035585556370666553408] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1506, (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1505 : B1505.tree = HexagonCover.NBand.M8500_8700.SplitData.node1505 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1506
  · rfl

def B1495 : Block := .branch 121 ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B1496, (.leaf 5 (Common.fact 319).pointIds 319), B1505]
theorem treeEq1495 : B1495.tree = HexagonCover.NBand.M8500_8700.SplitData.node1495 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1496
  · rfl
  · exact treeEq1505

theorem accepted1495 : B1495.accepted = true := by decide +kernel
theorem checked1495 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1495 (maskNeeds ![1237940039864092827016233345, 151447768845705174582786, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 730762045303841402865604842773740255699854164032]) := by
  rw [← treeEq1495]
  exact B1495.sound accepted1495
#print axioms checked1495

end HexagonCover.NBand.M8500_8700.SplitTree.Run0019
