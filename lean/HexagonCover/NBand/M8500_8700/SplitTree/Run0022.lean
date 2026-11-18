import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0021
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0022
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1448_1453 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1453 ![1238242271318996484309909889, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0021.checked1453
def B1623 : Block := .branch 160 ![385, 151447768845705174582786, 357842042605930235713034244, 24584, 98320, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq1623 : B1623.tree = HexagonCover.NBand.M8500_8700.SplitData.node1623 := by
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

def B1622 : Block := .branch 161 ![385, 151447768845705174582786, 357842042605930235713034244, 158461160731807133703786749960, 98320, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 856).pointIds 856), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B1623]
theorem treeEq1622 : B1622.tree = HexagonCover.NBand.M8500_8700.SplitData.node1622 := by
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
  · exact treeEq1623

def B1452 : Block := .branch 88 ![1238242271318996484309909889, 151447768845705174582786, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), Tip1448_1453, B1622, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq1452 : B1452.tree = HexagonCover.NBand.M8500_8700.SplitData.node1452 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1622
  · rfl
  · rfl
  · rfl
  · rfl

def B1626 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1626 : B1626.tree = HexagonCover.NBand.M8500_8700.SplitData.node1626 := by
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

def B1625 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1626, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1625 : B1625.tree = HexagonCover.NBand.M8500_8700.SplitData.node1625 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1626
  · rfl

def B1624 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158538531984262469970967945224, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1625]
theorem treeEq1624 : B1624.tree = HexagonCover.NBand.M8500_8700.SplitData.node1624 := by
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
  · exact treeEq1625

def B1451 : Block := .branch 86 ![1238242271318996484309909889, 151447768845705174582786, 48394830163192197859514372, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B1452, B1624, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq1451 : B1451.tree = HexagonCover.NBand.M8500_8700.SplitData.node1451 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1452
  · exact treeEq1624
  · rfl
  · rfl
  · rfl

def B1629 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1629 : B1629.tree = HexagonCover.NBand.M8500_8700.SplitData.node1629 := by
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

def B1628 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1629, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1628 : B1628.tree = HexagonCover.NBand.M8500_8700.SplitData.node1628 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1629
  · rfl

def B1627 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158499846358034801837377347592, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1628]
theorem treeEq1627 : B1627.tree = HexagonCover.NBand.M8500_8700.SplitData.node1627 := by
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
  · exact treeEq1628

def B1450 : Block := .branch 85 ![1238242271318996484309909889, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B1451, B1627, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq1450 : B1450.tree = HexagonCover.NBand.M8500_8700.SplitData.node1450 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1451
  · exact treeEq1627
  · rfl
  · rfl
  · rfl

def B1632 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1632 : B1632.tree = HexagonCover.NBand.M8500_8700.SplitData.node1632 := by
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

def B1631 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1632, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1631 : B1631.tree = HexagonCover.NBand.M8500_8700.SplitData.node1631 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1632
  · rfl

def B1630 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158480503544920967770582048776, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 863).pointIds 863), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1631]
theorem treeEq1630 : B1630.tree = HexagonCover.NBand.M8500_8700.SplitData.node1630 := by
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
  · exact treeEq1631

def B1449 : Block := .branch 84 ![1238242271318996484309909889, 151447768845705174582786, 9709203935524064268916740, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), B1450, B1630, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq1449 : B1449.tree = HexagonCover.NBand.M8500_8700.SplitData.node1449 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1450
  · exact treeEq1630
  · rfl
  · rfl
  · rfl

def B1635 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1635 : B1635.tree = HexagonCover.NBand.M8500_8700.SplitData.node1635 := by
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

def B1634 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1635, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1634 : B1634.tree = HexagonCover.NBand.M8500_8700.SplitData.node1634 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1635
  · rfl

def B1633 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158470832138364050737184399368, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1634]
theorem treeEq1633 : B1633.tree = HexagonCover.NBand.M8500_8700.SplitData.node1633 := by
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
  · exact treeEq1634

def B1448 : Block := .branch 83 ![1238242271318996484309909889, 151447768845705174582786, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B1449, B1633, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq1448 : B1448.tree = HexagonCover.NBand.M8500_8700.SplitData.node1448 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1449
  · exact treeEq1633
  · rfl
  · rfl
  · rfl

theorem accepted1448 : B1448.accepted = true := by decide +kernel
theorem checked1448 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1448 (maskNeeds ![1238242271318996484309909889, 151447768845705174582786, 37797378607030871267332, 237689323246071471297330700296, 1329227995784915872903807060280442896, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq1448]
  exact B1448.sound accepted1448
#print axioms checked1448

def B1652 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1652 : B1652.tree = HexagonCover.NBand.M8500_8700.SplitData.node1652 := by
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

def B1651 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1652, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1651 : B1651.tree = HexagonCover.NBand.M8500_8700.SplitData.node1651 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1652
  · rfl

def B1650 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1651]
theorem treeEq1650 : B1650.tree = HexagonCover.NBand.M8500_8700.SplitData.node1650 := by
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
  · exact treeEq1651

def B1649 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1650, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq1649 : B1649.tree = HexagonCover.NBand.M8500_8700.SplitData.node1649 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1650
  · rfl
  · rfl
  · rfl

def B1648 : Block := .branch 159 ![5192298715444887135313460795015553, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 363).pointIds 363), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1649]
theorem treeEq1648 : B1648.tree = HexagonCover.NBand.M8500_8700.SplitData.node1648 := by
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
  · exact treeEq1649

def B1658 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1658 : B1658.tree = HexagonCover.NBand.M8500_8700.SplitData.node1658 := by
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

def B1657 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1658, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1657 : B1657.tree = HexagonCover.NBand.M8500_8700.SplitData.node1657 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1658
  · rfl

def B1656 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1657]
theorem treeEq1656 : B1656.tree = HexagonCover.NBand.M8500_8700.SplitData.node1656 := by
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
  · exact treeEq1657

def B1655 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1656, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1655 : B1655.tree = HexagonCover.NBand.M8500_8700.SplitData.node1655 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1656
  · rfl
  · rfl
  · rfl

def B1654 : Block := .branch 159 ![10385863224579942993245453827441025, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1655]
theorem treeEq1654 : B1654.tree = HexagonCover.NBand.M8500_8700.SplitData.node1654 := by
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
  · exact treeEq1655

def B1662 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1662 : B1662.tree = HexagonCover.NBand.M8500_8700.SplitData.node1662 := by
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

def B1661 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1662, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1661 : B1661.tree = HexagonCover.NBand.M8500_8700.SplitData.node1661 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1662
  · rfl

def B1660 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1661]
theorem treeEq1660 : B1660.tree = HexagonCover.NBand.M8500_8700.SplitData.node1660 := by
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
  · exact treeEq1661

def B1659 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1660, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1659 : B1659.tree = HexagonCover.NBand.M8500_8700.SplitData.node1659 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1660
  · rfl
  · rfl
  · rfl

def B1653 : Block := .branch 113 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B1654, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1659]
theorem treeEq1653 : B1653.tree = HexagonCover.NBand.M8500_8700.SplitData.node1653 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1654
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1659

def B1647 : Block := .branch 112 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B1648, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1653]
theorem treeEq1647 : B1647.tree = HexagonCover.NBand.M8500_8700.SplitData.node1647 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1648
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1653

def B1664 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1664 : B1664.tree = HexagonCover.NBand.M8500_8700.SplitData.node1664 := by
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

def B1663 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1664, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1663 : B1663.tree = HexagonCover.NBand.M8500_8700.SplitData.node1663 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1664
  · rfl

def B1646 : Block := .branch 109 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B1647, (.leaf 5 (Common.fact 294).pointIds 294), B1663]
theorem treeEq1646 : B1646.tree = HexagonCover.NBand.M8500_8700.SplitData.node1646 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1647
  · rfl
  · exact treeEq1663

theorem accepted1646 : B1646.accepted = true := by decide +kernel
theorem checked1646 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1646 (maskNeeds ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1646]
  exact B1646.sound accepted1646
#print axioms checked1646

def B1686 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1686 : B1686.tree = HexagonCover.NBand.M8500_8700.SplitData.node1686 := by
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

def B1685 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1686, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1685 : B1685.tree = HexagonCover.NBand.M8500_8700.SplitData.node1685 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1686
  · rfl

def B1684 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1685]
theorem treeEq1684 : B1684.tree = HexagonCover.NBand.M8500_8700.SplitData.node1684 := by
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
  · exact treeEq1685

def B1683 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1684, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq1683 : B1683.tree = HexagonCover.NBand.M8500_8700.SplitData.node1683 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1684
  · rfl
  · rfl
  · rfl

def B1682 : Block := .branch 159 ![5193565747075095722024820048658817, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 912).pointIds 912), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1683]
theorem treeEq1682 : B1682.tree = HexagonCover.NBand.M8500_8700.SplitData.node1682 := by
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
  · exact treeEq1683

def B1692 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1692 : B1692.tree = HexagonCover.NBand.M8500_8700.SplitData.node1692 := by
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

def B1691 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1692, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1691 : B1691.tree = HexagonCover.NBand.M8500_8700.SplitData.node1691 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1692
  · rfl

def B1690 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1691]
theorem treeEq1690 : B1690.tree = HexagonCover.NBand.M8500_8700.SplitData.node1690 := by
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
  · exact treeEq1691

def B1689 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1690, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1689 : B1689.tree = HexagonCover.NBand.M8500_8700.SplitData.node1689 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1690
  · rfl
  · rfl
  · rfl

def B1688 : Block := .branch 159 ![10385862605609923350555316377878913, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 913).pointIds 913), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1689]
theorem treeEq1688 : B1688.tree = HexagonCover.NBand.M8500_8700.SplitData.node1688 := by
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
  · exact treeEq1689

def B1696 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1696 : B1696.tree = HexagonCover.NBand.M8500_8700.SplitData.node1696 := by
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

def B1695 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1696, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1695 : B1695.tree = HexagonCover.NBand.M8500_8700.SplitData.node1695 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1696
  · rfl

def B1694 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1695]
theorem treeEq1694 : B1694.tree = HexagonCover.NBand.M8500_8700.SplitData.node1694 := by
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
  · exact treeEq1695

def B1693 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1694, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1693 : B1693.tree = HexagonCover.NBand.M8500_8700.SplitData.node1693 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1694
  · rfl
  · rfl
  · rfl

def B1687 : Block := .branch 113 ![1268888540268093494323719438721, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B1688, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1693]
theorem treeEq1687 : B1687.tree = HexagonCover.NBand.M8500_8700.SplitData.node1687 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1688
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1693

def B1681 : Block := .branch 112 ![1268888540268093494323719438721, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B1682, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1687]
theorem treeEq1681 : B1681.tree = HexagonCover.NBand.M8500_8700.SplitData.node1681 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1682
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1687

def B1698 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1698 : B1698.tree = HexagonCover.NBand.M8500_8700.SplitData.node1698 := by
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

def B1697 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1698, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1697 : B1697.tree = HexagonCover.NBand.M8500_8700.SplitData.node1697 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1698
  · rfl

def B1680 : Block := .branch 109 ![1268888540268093494323719438721, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B1681, (.leaf 5 (Common.fact 294).pointIds 294), B1697]
theorem treeEq1680 : B1680.tree = HexagonCover.NBand.M8500_8700.SplitData.node1680 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1681
  · rfl
  · exact treeEq1697

theorem accepted1680 : B1680.accepted = true := by decide +kernel
theorem checked1680 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1680 (maskNeeds ![1268888540268093494323719438721, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1680]
  exact B1680.sound accepted1680
#print axioms checked1680

def Tip1643_1646 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1646 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] checked1646
def B1669 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1669 : B1669.tree = HexagonCover.NBand.M8500_8700.SplitData.node1669 := by
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

def B1668 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1669, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1668 : B1668.tree = HexagonCover.NBand.M8500_8700.SplitData.node1668 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1669
  · rfl

def B1667 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 387).pointIds 387), B1668]
theorem treeEq1667 : B1667.tree = HexagonCover.NBand.M8500_8700.SplitData.node1667 := by
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
  · exact treeEq1668

def B1666 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 708).pointIds 708), B1667, (.leaf 0 [] 0)]
theorem treeEq1666 : B1666.tree = HexagonCover.NBand.M8500_8700.SplitData.node1666 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1667
  · rfl

def B1665 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329552514338574299630590216301019152, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 707).pointIds 707), B1666, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1665 : B1665.tree = HexagonCover.NBand.M8500_8700.SplitData.node1665 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1666
  · rfl

def B1645 : Block := .branch 108 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), Tip1643_1646, B1665, (.leaf 5 (Common.fact 288).pointIds 288), (.leaf 6 (Common.fact 289).pointIds 289)]
theorem treeEq1645 : B1645.tree = HexagonCover.NBand.M8500_8700.SplitData.node1645 := by
  change Tree.branch (108 : Fin 175) _ = Tree.branch (108 : Fin 175) _
  apply congrArg (Tree.branch (108 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1665
  · rfl
  · rfl

def B1671 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378352962609987455952305861073871855624, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq1671 : B1671.tree = HexagonCover.NBand.M8500_8700.SplitData.node1671 := by
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

def B1670 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 316912650057057350374175825928, 1329227995784915872903807060280442896, 393248, 11193971277528324461999332237303422513578048] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1671, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1670 : B1670.tree = HexagonCover.NBand.M8500_8700.SplitData.node1670 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1671
  · rfl
  · rfl
  · rfl

def B1644 : Block := .branch 100 ![1856910059506782964465795457, 151447768845705174582786, 4873482210321473860540420, 554597137599850363154807676936, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![B1645, (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 283).pointIds 283), (.leaf 5 (Common.fact 284).pointIds 284), B1670]
theorem treeEq1644 : B1644.tree = HexagonCover.NBand.M8500_8700.SplitData.node1644 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1645
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1670

def B1676 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1676 : B1676.tree = HexagonCover.NBand.M8500_8700.SplitData.node1676 := by
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

def B1675 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1676, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1675 : B1675.tree = HexagonCover.NBand.M8500_8700.SplitData.node1675 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1676
  · rfl

def B1674 : Block := .branch 163 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 387).pointIds 387), B1675]
theorem treeEq1674 : B1674.tree = HexagonCover.NBand.M8500_8700.SplitData.node1674 := by
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
  · exact treeEq1675

def B1673 : Block := .branch 165 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 730).pointIds 730), B1674, (.leaf 0 [] 0)]
theorem treeEq1673 : B1673.tree = HexagonCover.NBand.M8500_8700.SplitData.node1673 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1674
  · rfl

def B1672 : Block := .branch 167 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329228312697565929961157434456244240, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 729).pointIds 729), B1673, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq1672 : B1672.tree = HexagonCover.NBand.M8500_8700.SplitData.node1672 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1673
  · rfl

def B1643 : Block := .branch 98 ![1856910059506782964465795457, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B1644, B1672, (.leaf 5 (Common.fact 278).pointIds 278), (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq1643 : B1643.tree = HexagonCover.NBand.M8500_8700.SplitData.node1643 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1644
  · exact treeEq1672
  · rfl
  · rfl

theorem accepted1643 : B1643.accepted = true := by decide +kernel
theorem checked1643 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1643 (maskNeeds ![1856910059506782964465795457, 151447768845705174582786, 4873500657065547570092036, 237684487542793012780631875592, 1329227995784915872903807060280442896, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1643]
  exact B1643.sound accepted1643
#print axioms checked1643

end HexagonCover.NBand.M8500_8700.SplitTree.Run0022
