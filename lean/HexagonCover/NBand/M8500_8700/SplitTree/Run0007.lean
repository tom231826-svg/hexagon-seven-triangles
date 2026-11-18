import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0007
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0560_0571 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0571 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792] HexagonCover.NBand.M8500_8700.SplitTree.Run0006.checked0571
def B0565 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0565 : B0565.tree = HexagonCover.NBand.M8500_8700.SplitData.node0565 := by
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

def B0564 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0565, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0564 : B0564.tree = HexagonCover.NBand.M8500_8700.SplitData.node0564 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0565
  · rfl

def B0563 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0564]
theorem treeEq0563 : B0563.tree = HexagonCover.NBand.M8500_8700.SplitData.node0563 := by
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
  · exact treeEq0564

def B0570 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 836).pointIds 836)]
theorem treeEq0570 : B0570.tree = HexagonCover.NBand.M8500_8700.SplitData.node0570 := by
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

def B0569 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0570, (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0569 : B0569.tree = HexagonCover.NBand.M8500_8700.SplitData.node0569 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0570
  · rfl

def B0568 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0569]
theorem treeEq0568 : B0568.tree = HexagonCover.NBand.M8500_8700.SplitData.node0568 := by
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
  · exact treeEq0569

def B0567 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0568, (.leaf 0 [] 0)]
theorem treeEq0567 : B0567.tree = HexagonCover.NBand.M8500_8700.SplitData.node0567 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0568
  · rfl

def B0566 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0567, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0566 : B0566.tree = HexagonCover.NBand.M8500_8700.SplitData.node0566 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0567
  · rfl

def B0562 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0563, B0566, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0562 : B0562.tree = HexagonCover.NBand.M8500_8700.SplitData.node0562 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0563
  · exact treeEq0566
  · rfl
  · rfl

def B0561 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0562, (.leaf 5 (Common.fact 319).pointIds 319), Tip0560_0571]
theorem treeEq0561 : B0561.tree = HexagonCover.NBand.M8500_8700.SplitData.node0561 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0562
  · rfl
  · rfl

def B0586 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 836).pointIds 836)]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M8500_8700.SplitData.node0586 := by
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

def B0585 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0586, (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M8500_8700.SplitData.node0585 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0586
  · rfl

def B0584 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0585]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M8500_8700.SplitData.node0584 := by
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
  · exact treeEq0585

def B0583 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0584, (.leaf 0 [] 0)]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M8500_8700.SplitData.node0583 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0584
  · rfl

def B0582 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0583, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M8500_8700.SplitData.node0582 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0583
  · rfl

def B0560 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0561, B0582, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0560 : B0560.tree = HexagonCover.NBand.M8500_8700.SplitData.node0560 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0561
  · exact treeEq0582
  · rfl
  · rfl

theorem accepted0560 : B0560.accepted = true := by decide +kernel
theorem checked0560 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0560 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640]) := by
  rw [← treeEq0560]
  exact B0560.sound accepted0560
#print axioms checked0560

def Tip0522_0523 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0523 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0006.checked0523
def B0558 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 11193971298296244245538414522023911127253056] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M8500_8700.SplitData.node0558 := by
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
  · rfl

def B0557 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0558, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M8500_8700.SplitData.node0557 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0558
  · rfl
  · rfl

def B0556 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0557, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M8500_8700.SplitData.node0556 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0557
  · rfl
  · rfl

def B0555 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0556, (.leaf 0 [] 0)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M8500_8700.SplitData.node0555 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0556
  · rfl

def B0554 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0555, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M8500_8700.SplitData.node0554 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0555
  · rfl

def B0553 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0554, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M8500_8700.SplitData.node0553 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0554
  · rfl
  · rfl

def B0552 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 392).pointIds 392), B0553, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M8500_8700.SplitData.node0552 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0553
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0551 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0552, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M8500_8700.SplitData.node0551 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0552
  · rfl
  · rfl
  · rfl
  · rfl

def B0550 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 11226638405520654338030898484337360875552832] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0551, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M8500_8700.SplitData.node0550 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0551
  · rfl
  · rfl
  · rfl

def B0522 : Block := .branch 114 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448] ![Tip0522_0523, (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 308).pointIds 308), (.leaf 5 (Common.fact 309).pointIds 309), B0550]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M8500_8700.SplitData.node0522 := by
  change Tree.branch (114 : Fin 175) _ = Tree.branch (114 : Fin 175) _
  apply congrArg (Tree.branch (114 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0550

theorem accepted0522 : B0522.accepted = true := by decide +kernel
theorem checked0522 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0522 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0522]
  exact B0522.sound accepted0522
#print axioms checked0522

def B0619 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M8500_8700.SplitData.node0619 := by
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
  · rfl

def B0618 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0619, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M8500_8700.SplitData.node0618 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0619
  · rfl
  · rfl

def B0617 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0618, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M8500_8700.SplitData.node0617 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0618
  · rfl
  · rfl

def B0616 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0617, (.leaf 0 [] 0)]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M8500_8700.SplitData.node0616 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0617
  · rfl

def B0615 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0616, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M8500_8700.SplitData.node0615 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0616
  · rfl

def B0614 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0615, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M8500_8700.SplitData.node0614 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0615
  · rfl
  · rfl

def B0613 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 392).pointIds 392), B0614, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M8500_8700.SplitData.node0613 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0614
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0612 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0613, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M8500_8700.SplitData.node0612 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0613
  · rfl
  · rfl
  · rfl
  · rfl

def B0611 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0612, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M8500_8700.SplitData.node0611 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0612
  · rfl
  · rfl
  · rfl

def B0610 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 1496577676626844588240573268701473812127674924400672, 11226641043207458473723333777829496119361600] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0611]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M8500_8700.SplitData.node0610 := by
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
  · exact treeEq0611

def B0609 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641048399755332258161406359992448581696] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0610, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M8500_8700.SplitData.node0609 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610
  · rfl

theorem accepted0609 : B0609.accepted = true := by decide +kernel
theorem checked0609 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0609 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641048399755332258161406359992448581696]) := by
  rw [← treeEq0609]
  exact B0609.sound accepted0609
#print axioms checked0609

def Tip0598_0609 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0609 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641048399755332258161406359992448581696] checked0609
def B0603 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660459200500207336879260687771987607616] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 840).pointIds 840)]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M8500_8700.SplitData.node0603 := by
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

def B0602 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660459200500207336879260687771987607616] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0603, (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M8500_8700.SplitData.node0602 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0603
  · rfl

def B0601 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0602]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M8500_8700.SplitData.node0601 := by
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
  · exact treeEq0602

def B0608 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M8500_8700.SplitData.node0608 := by
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

def B0607 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0608, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M8500_8700.SplitData.node0607 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl

def B0606 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0607]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M8500_8700.SplitData.node0606 := by
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
  · exact treeEq0607

def B0605 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0606, (.leaf 0 [] 0)]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M8500_8700.SplitData.node0605 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0606
  · rfl

def B0604 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0605, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M8500_8700.SplitData.node0604 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0605
  · rfl

def B0600 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0601, B0604, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M8500_8700.SplitData.node0600 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0601
  · exact treeEq0604
  · rfl
  · rfl

def B0599 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0600, (.leaf 5 (Common.fact 319).pointIds 319), Tip0598_0609]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M8500_8700.SplitData.node0599 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0600
  · rfl
  · rfl

def B0624 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M8500_8700.SplitData.node0624 := by
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

def B0623 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618506064983148595661900589669599936576] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0624, (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M8500_8700.SplitData.node0623 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0624
  · rfl

def B0622 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0623]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M8500_8700.SplitData.node0622 := by
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
  · exact treeEq0623

def B0621 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0622, (.leaf 0 [] 0)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M8500_8700.SplitData.node0621 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0622
  · rfl

def B0620 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0621, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M8500_8700.SplitData.node0620 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl

def B0598 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0599, B0620, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M8500_8700.SplitData.node0598 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0599
  · exact treeEq0620
  · rfl
  · rfl

theorem accepted0598 : B0598.accepted = true := by decide +kernel
theorem checked0598 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0598 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638389943763762426415598745871887892544]) := by
  rw [← treeEq0598]
  exact B0598.sound accepted0598
#print axioms checked0598

def B0656 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661359505371550386653293374621601595408, 393248, 748288849507353694807469898273653799753954862039104] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 832).pointIds 832), (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M8500_8700.SplitData.node0656 := by
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
  · rfl

def B0655 : Block := .branch 129 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), (.leaf 3 (Common.fact 831).pointIds 831), B0656, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M8500_8700.SplitData.node0655 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0656
  · rfl
  · rfl

def B0654 : Block := .branch 138 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 830).pointIds 830), B0655, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M8500_8700.SplitData.node0654 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0655
  · rfl
  · rfl

def B0653 : Block := .branch 165 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 829).pointIds 829), B0654, (.leaf 0 [] 0)]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M8500_8700.SplitData.node0653 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0654
  · rfl

def B0652 : Block := .branch 167 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 89202980794771529673459726544159758065172496, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 828).pointIds 828), B0653, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M8500_8700.SplitData.node0652 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0653
  · rfl

def B0651 : Block := .branch 146 ![385, 1538, 6148, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063337327745108074070683893333581365312] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 347).pointIds 347), (.leaf 3 (Common.fact 827).pointIds 827), B0652, (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 0 [] 0)]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M8500_8700.SplitData.node0651 := by
  change Tree.branch (146 : Fin 175) _ = Tree.branch (146 : Fin 175) _
  apply congrArg (Tree.branch (146 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0652
  · rfl
  · rfl

def B0650 : Block := .branch 160 ![385, 1538, 5986310706507378352962293084515080737290690255394820, 2993155353253689176481146542238650902713866546864136, 649037107316853453566312041250832, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 392).pointIds 392), B0651, (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M8500_8700.SplitData.node0650 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0651
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0649 : Block := .branch 172 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 2993155353253689176481146542238650902713866546864136, 1329877032892232726357373372321595408, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 769).pointIds 769), B0650, (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M8500_8700.SplitData.node0649 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0650
  · rfl
  · rfl
  · rfl
  · rfl

def B0648 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 4835703278458516698849288, 1329877032892232726357373372321595408, 393248, 748288849540063347712338825143725940954326239805504] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), B0649, (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M8500_8700.SplitData.node0648 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0649
  · rfl
  · rfl
  · rfl

def B0647 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 1496577676626844588240573268701473812127674924400672, 11226641053592052190792989034890488777801792] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), B0648]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M8500_8700.SplitData.node0647 := by
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
  · exact treeEq0648

def B0646 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0647, (.leaf 6 (Common.fact 837).pointIds 837)]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M8500_8700.SplitData.node0646 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0647
  · rfl

theorem accepted0646 : B0646.accepted = true := by decide +kernel
theorem checked0646 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0646 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792]) := by
  rw [← treeEq0646]
  exact B0646.sound accepted0646
#print axioms checked0646

def Tip0635_0646 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0646 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 158461160731807133703786749960, 1329877032892232726357373372321595408, 393248, 11226641053592052190792989034890488777801792] checked0646
def B0640 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M8500_8700.SplitData.node0640 := by
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

def B0639 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0640, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M8500_8700.SplitData.node0639 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0640
  · rfl

def B0638 : Block := .branch 171 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 680564734317250737715613698941498974216, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 743).pointIds 743), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 819).pointIds 819), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B0639]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M8500_8700.SplitData.node0638 := by
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
  · exact treeEq0639

def B0645 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 836).pointIds 836)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M8500_8700.SplitData.node0645 := by
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

def B0644 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0645, (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M8500_8700.SplitData.node0644 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0645
  · rfl

def B0643 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B0644]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M8500_8700.SplitData.node0643 := by
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
  · exact treeEq0644

def B0642 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B0643, (.leaf 0 [] 0)]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M8500_8700.SplitData.node0642 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0643
  · rfl

def B0641 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 684553066866338991398914202356418707472, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B0642, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M8500_8700.SplitData.node0641 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0642
  · rfl

def B0637 : Block := .branch 129 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 475373810788864484077962551304, 3988333024462064472164987492882284560, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B0638, B0641, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M8500_8700.SplitData.node0637 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0638
  · exact treeEq0641
  · rfl
  · rfl

def B0636 : Block := .branch 121 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 315).pointIds 315), (.leaf 1 (Common.fact 316).pointIds 316), (.leaf 2 (Common.fact 317).pointIds 317), (.leaf 3 (Common.fact 318).pointIds 318), B0637, (.leaf 5 (Common.fact 319).pointIds 319), Tip0635_0646]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M8500_8700.SplitData.node0636 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0637
  · rfl
  · rfl

def B0661 : Block := .branch 169 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 775).pointIds 775), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 836).pointIds 836)]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M8500_8700.SplitData.node0661 := by
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

def B0660 : Block := .branch 170 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618511257280007130489529120165929156672] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 773).pointIds 773), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 821).pointIds 821), (.leaf 4 (Common.fact 749).pointIds 749), B0661, (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M8500_8700.SplitData.node0660 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0661
  · rfl

def B0659 : Block := .branch 163 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 233840261972944466912589573234605283144949207269408, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 387).pointIds 387), B0660]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M8500_8700.SplitData.node0659 := by
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
  · exact treeEq0660

def B0658 : Block := .branch 165 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 187072209578355573530071658587684226515959365894176, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 645).pointIds 645), B0659, (.leaf 0 [] 0)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M8500_8700.SplitData.node0658 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · rfl

def B0657 : Block := .branch 167 ![1238242271318996484309909889, 226673591178292726072834, 37778931862957161715716, 158461160731807133703786749960, 1994491030784690662809276902461767696, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 644).pointIds 644), B0658, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M8500_8700.SplitData.node0657 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0658
  · rfl

def B0635 : Block := .branch 119 ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0636, B0657, (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M8500_8700.SplitData.node0635 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0636
  · exact treeEq0657
  · rfl
  · rfl

theorem accepted0635 : B0635.accepted = true := by decide +kernel
theorem checked0635 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0635 (maskNeeds ![1238242271318996484309909889, 226673591178292726072834, 9709185488779990559365124, 475373810788864484077962551304, 1329877032892232726357373372321595408, 393248, 11226638395136060620961243227276368217112640]) := by
  rw [← treeEq0635]
  exact B0635.sound accepted0635
#print axioms checked0635

end HexagonCover.NBand.M8500_8700.SplitTree.Run0007
