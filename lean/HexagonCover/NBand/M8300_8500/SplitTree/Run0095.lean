import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0091
import HexagonCover.NBand.M8300_8500.SplitTree.Run0092
import HexagonCover.NBand.M8300_8500.SplitTree.Run0094
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0095
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6613_6618 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6618 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0092.checked6618
def Tip6613_6727 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6727 ![1267651204691139208811290558849, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] HexagonCover.NBand.M8300_8500.SplitTree.Run0094.checked6727
def Tip6613_6883 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6883 ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] HexagonCover.NBand.M8300_8500.SplitTree.Run0094.checked6883
def B6723 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq6723 : B6723.tree = HexagonCover.NBand.M8300_8500.SplitData.node6723 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6722 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6723, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq6722 : B6722.tree = HexagonCover.NBand.M8300_8500.SplitData.node6722 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6723
  · rfl

def B6721 : Block := .branch 163 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649354019966910510916686217052176, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B6722]
theorem treeEq6721 : B6721.tree = HexagonCover.NBand.M8300_8500.SplitData.node6721 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6722

def B6720 : Block := .branch 165 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649354019966910510916686217052176, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B6721, (.leaf 0 [] 0)]
theorem treeEq6720 : B6720.tree = HexagonCover.NBand.M8300_8500.SplitData.node6720 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6721
  · rfl

def B6719 : Block := .branch 167 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649354019966910510916686217052176, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B6720, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6719 : B6719.tree = HexagonCover.NBand.M8300_8500.SplitData.node6719 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6720
  · rfl

def B6617 : Block := .branch 98 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip6613_6618, B6719, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq6617 : B6617.tree = HexagonCover.NBand.M8300_8500.SplitData.node6617 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6719
  · rfl
  · rfl

def B6726 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq6726 : B6726.tree = HexagonCover.NBand.M8300_8500.SplitData.node6726 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6725 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6726, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq6725 : B6725.tree = HexagonCover.NBand.M8300_8500.SplitData.node6725 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6726
  · rfl

def B6724 : Block := .branch 170 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79305533766719673860725170184, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6725]
theorem treeEq6724 : B6724.tree = HexagonCover.NBand.M8300_8500.SplitData.node6724 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6725

def B6616 : Block := .branch 86 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6617, B6724, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1073).pointIds 1073)]
theorem treeEq6616 : B6616.tree = HexagonCover.NBand.M8300_8500.SplitData.node6616 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6617
  · exact treeEq6724
  · rfl
  · rfl
  · rfl

def B6615 : Block := .branch 168 ![1267651506922594112468584235393, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1078).pointIds 1078), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B6616]
theorem treeEq6615 : B6615.tree = HexagonCover.NBand.M8300_8500.SplitData.node6615 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6616

def B6614 : Block := .branch 78 ![1267651204691139208811290558849, 75558010163820712953346, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![B6615, Tip6613_6727, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 1072).pointIds 1072)]
theorem treeEq6614 : B6614.tree = HexagonCover.NBand.M8300_8500.SplitData.node6614 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6615
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6613 : Block := .branch 76 ![1267651204691139208811290558849, 146437906389534210, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 223).pointIds 223), B6614, Tip6613_6883, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq6613 : B6613.tree = HexagonCover.NBand.M8300_8500.SplitData.node6613 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6614
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6613 : B6613.accepted = true := by decide +kernel
theorem checked6613 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6613 (maskNeeds ![1267651204691139208811290558849, 146437906389534210, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6613]
  exact B6613.sound accepted6613
#print axioms checked6613

def B6922 : Block := .branch 163 ![385, 1538, 6148, 24584, 2943703812053140985483046098887109687361241104, 393248, 15714065604581868176527286971965703256742633160572992] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1281).pointIds 1281), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1282).pointIds 1282)]
theorem treeEq6922 : B6922.tree = HexagonCover.NBand.M8300_8500.SplitData.node6922 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6921 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 2854500831259018492916903225796516241337319440, 393248, 15714065604581868176527286971965703256742633160572992] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6922, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6921 : B6921.tree = HexagonCover.NBand.M8300_8500.SplitData.node6921 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6922
  · rfl
  · rfl

def B6920 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 2854500831259018492916903225796516241337319440, 393248, 15714065604581889444175219530619669717655597646086208] ![(.leaf 0 (Common.fact 577).pointIds 577), B6921, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1280).pointIds 1280)]
theorem treeEq6920 : B6920.tree = HexagonCover.NBand.M8300_8500.SplitData.node6920 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6921
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6919 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 2854500831259018492916903225796516241337319440, 393248, 15714065604581889444175219530619669717655597646086208] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6920, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1279).pointIds 1279)]
theorem treeEq6919 : B6919.tree = HexagonCover.NBand.M8300_8500.SplitData.node6919 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6920
  · rfl
  · rfl
  · rfl
  · rfl

def B6918 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 24584, 2854500831259018492916903225796516241337319440, 393248, 15714065604581889444175219530619669717655597646086208] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6919, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1278).pointIds 1278)]
theorem treeEq6918 : B6918.tree = HexagonCover.NBand.M8300_8500.SplitData.node6918 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6919
  · rfl
  · rfl
  · rfl

def B6917 : Block := .branch 173 ![1237940039285380274899124609, 151153343838634758899202, 53235255808133584203552772, 158456325028528675187087925256, 2854500831259018492916903225796516241337319440, 5709034369502101269473775122669557740833472544, 3741444191567132738250633381007879220634198254026816] ![(.leaf 0 (Common.fact 1276).pointIds 1276), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1277).pointIds 1277), (.leaf 5 (Common.fact 1232).pointIds 1232), B6918]
theorem treeEq6917 : B6917.tree = HexagonCover.NBand.M8300_8500.SplitData.node6917 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6918

def B6916 : Block := .branch 172 ![1237940039285380274899124609, 151153343838634758899202, 53235255808133584203552772, 158456325028528675187087925256, 2854500831259018492916903225796516241337319440, 5709034369502101269473775122669557740833472544, 3741444191567132738250633381007879220634198254026816] ![B6917, (.leaf 1 (Common.fact 1273).pointIds 1273), (.leaf 2 (Common.fact 1210).pointIds 1210), (.leaf 3 (Common.fact 1211).pointIds 1211), (.leaf 4 (Common.fact 1274).pointIds 1274), (.leaf 5 (Common.fact 1229).pointIds 1229), (.leaf 6 (Common.fact 1275).pointIds 1275)]
theorem treeEq6916 : B6916.tree = HexagonCover.NBand.M8300_8500.SplitData.node6916 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6917
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6915 : Block := .branch 120 ![1237940039285380274899124609, 151153343838634758899202, 53235255808133584203552772, 158456325028528675187087925256, 2854500829929790497131987352892709181056974864, 5709034369502101269473775122669557740833472544, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B6916, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1272).pointIds 1272)]
theorem treeEq6915 : B6915.tree = HexagonCover.NBand.M8300_8500.SplitData.node6915 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6916
  · rfl
  · rfl

def B6914 : Block := .branch 130 ![1237940039285380274899124609, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 2854500829929790497131987352892709181056974864, 5709034369502101269473775122669557740833472544, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), B6915, (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1271).pointIds 1271)]
theorem treeEq6914 : B6914.tree = HexagonCover.NBand.M8300_8500.SplitData.node6914 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6915
  · rfl
  · rfl

def B6913 : Block := .branch 131 ![1237940039285380274899124609, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 2854500829929790497131987352892709181056974864, 5709034369502101269473775122669557740833472544, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), B6914, (.leaf 5 (Common.fact 733).pointIds 733), (.leaf 6 (Common.fact 1270).pointIds 1270)]
theorem treeEq6913 : B6913.tree = HexagonCover.NBand.M8300_8500.SplitData.node6913 := by
  change Tree.branch (131 : Fin 177) _ = Tree.branch (131 : Fin 177) _
  apply congrArg (Tree.branch (131 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6914
  · rfl
  · rfl

def B6912 : Block := .branch 125 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 2854500829929790497131987352892709181056974864, 5709034326966805404356467189747731811862446112, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B6913, (.leaf 6 (Common.fact 1269).pointIds 1269)]
theorem treeEq6912 : B6912.tree = HexagonCover.NBand.M8300_8500.SplitData.node6912 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6913
  · rfl

def B6911 : Block := .branch 132 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B6912, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 1268).pointIds 1268)]
theorem treeEq6911 : B6911.tree = HexagonCover.NBand.M8300_8500.SplitData.node6911 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6912
  · rfl
  · rfl

def B6910 : Block := .branch 142 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B6911, (.leaf 5 (Common.fact 286).pointIds 286), (.leaf 6 (Common.fact 1267).pointIds 1267)]
theorem treeEq6910 : B6910.tree = HexagonCover.NBand.M8300_8500.SplitData.node6910 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6911
  · rfl
  · rfl

def B6909 : Block := .branch 151 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 98320, 5709034326966805404356467189747731811862446112, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6910, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1266).pointIds 1266)]
theorem treeEq6909 : B6909.tree = HexagonCover.NBand.M8300_8500.SplitData.node6909 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6910
  · rfl
  · rfl

def B6908 : Block := .branch 152 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81327708820892342539772865044488, 696898287454081973172991196020261297160208, 43556142965880123323311949751266331459616, 3741444202739283408998885013437394331834012172550208] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 1264).pointIds 1264), B6909, (.leaf 6 (Common.fact 1265).pointIds 1265)]
theorem treeEq6908 : B6908.tree = HexagonCover.NBand.M8300_8500.SplitData.node6908 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6909
  · rfl

def B6907 : Block := .branch 169 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 696898287454081973172991196020261297160208, 43556142965880123323311949751266331459616, 2993155364425861114878598379086657425770174710546496] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1263).pointIds 1263), (.leaf 5 (Common.fact 589).pointIds 589), B6908]
theorem treeEq6907 : B6907.tree = HexagonCover.NBand.M8300_8500.SplitData.node6907 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6908

def B6906 : Block := .branch 135 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 696898287454081973172991196020261297160208, 393248, 2993155364425861114878598379086657425770174710546496] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B6907, (.leaf 6 (Common.fact 1262).pointIds 1262)]
theorem treeEq6906 : B6906.tree = HexagonCover.NBand.M8300_8500.SplitData.node6906 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6907
  · rfl

def B6905 : Block := .branch 140 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 696898287454081973172991196020261297160208, 393248, 2993155364425861114878598379086657425770174710546496] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B6906, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 1261).pointIds 1261)]
theorem treeEq6905 : B6905.tree = HexagonCover.NBand.M8300_8500.SplitData.node6905 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6906
  · rfl
  · rfl

def B6904 : Block := .branch 143 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 696898287454081973172991196020261297160208, 393248, 2993155353275488515613286808318798289445993957556288] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 217).pointIds 217), B6905]
theorem treeEq6904 : B6904.tree = HexagonCover.NBand.M8300_8500.SplitData.node6904 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6905

def B6903 : Block := .branch 139 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 98320, 393248, 2993155353275493832525269947982289904674235078934592] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B6904, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1260).pointIds 1260)]
theorem treeEq6903 : B6903.tree = HexagonCover.NBand.M8300_8500.SplitData.node6903 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6904
  · rfl
  · rfl

theorem accepted6903 : B6903.accepted = true := by decide +kernel
theorem checked6903 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6903 (maskNeeds ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 98320, 393248, 2993155353275493832525269947982289904674235078934592]) := by
  rw [← treeEq6903]
  exact B6903.sound accepted6903
#print axioms checked6903

def Tip6374_6380 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6380 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0091.checked6380
def Tip6374_6613 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6613 ![1267651204691139208811290558849, 146437906389534210, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] checked6613
def Tip6374_6903 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6903 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 98320, 393248, 2993155353275493832525269947982289904674235078934592] checked6903
def B6612 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq6612 : B6612.tree = HexagonCover.NBand.M8300_8500.SplitData.node6612 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6611 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6612, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq6611 : B6611.tree = HexagonCover.NBand.M8300_8500.SplitData.node6611 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6612
  · rfl

def B6610 : Block := .branch 86 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3368761285198103825724805110178891496631655019839552] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6611, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1073).pointIds 1073)]
theorem treeEq6610 : B6610.tree = HexagonCover.NBand.M8300_8500.SplitData.node6610 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6611
  · rfl
  · rfl
  · rfl
  · rfl

def B6609 : Block := .branch 138 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6610, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6609 : B6609.tree = HexagonCover.NBand.M8300_8500.SplitData.node6609 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6610
  · rfl
  · rfl

def B6608 : Block := .branch 165 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89202980794771529673459726544159758065172496, 187072209578355573530071658587684226515959365894176, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6609, (.leaf 0 [] 0)]
theorem treeEq6608 : B6608.tree = HexagonCover.NBand.M8300_8500.SplitData.node6608 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6609
  · rfl

def B6607 : Block := .branch 167 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89202980794771529673459726544159758065172496, 393248, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6608, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6607 : B6607.tree = HexagonCover.NBand.M8300_8500.SplitData.node6607 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6608
  · rfl

def B6606 : Block := .branch 146 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 393248, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6607, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6606 : B6606.tree = HexagonCover.NBand.M8300_8500.SplitData.node6606 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6607
  · rfl
  · rfl

def B6605 : Block := .branch 161 ![604462909807314587353473, 146437906389534210, 53273034739996541365262340, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 393248, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B6606]
theorem treeEq6605 : B6605.tree = HexagonCover.NBand.M8300_8500.SplitData.node6605 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6606

def B6604 : Block := .branch 170 ![604462909807314587353473, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3368761285219908481767660870158005547648493792264256] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6605, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq6604 : B6604.tree = HexagonCover.NBand.M8300_8500.SplitData.node6604 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6605
  · rfl
  · rfl
  · rfl

def B6603 : Block := .branch 160 ![604462909807314587353473, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B6604]
theorem treeEq6603 : B6603.tree = HexagonCover.NBand.M8300_8500.SplitData.node6603 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6604

def B6379 : Block := .branch 76 ![604462909807314587353473, 146437906389534210, 53197476876270627041843204, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip6374_6380, B6603, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq6379 : B6379.tree = HexagonCover.NBand.M8300_8500.SplitData.node6379 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6603
  · rfl
  · rfl
  · rfl
  · rfl

def B6378 : Block := .branch 168 ![1267651204986287113990643384705, 146437906389534210, 53197476876270627041843204, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1070).pointIds 1070), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B6379]
theorem treeEq6378 : B6378.tree = HexagonCover.NBand.M8300_8500.SplitData.node6378 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6379

def B6377 : Block := .branch 68 ![1267651204691139208811290558849, 146437906389534210, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![B6378, Tip6374_6613, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1069).pointIds 1069)]
theorem treeEq6377 : B6377.tree = HexagonCover.NBand.M8300_8500.SplitData.node6377 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6376 : Block := .branch 143 ![1267651204691139208811290558849, 146437906389534210, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 216).pointIds 216), (.leaf 5 (Common.fact 217).pointIds 217), B6377]
theorem treeEq6376 : B6376.tree = HexagonCover.NBand.M8300_8500.SplitData.node6376 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6377

def B6901 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 14965776766290223954537709855993247549719244202049600] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1258).pointIds 1258)]
theorem treeEq6901 : B6901.tree = HexagonCover.NBand.M8300_8500.SplitData.node6901 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6900 : Block := .branch 174 ![1267650600228229401496703205761, 151153199653077938865666, 53230514994906640848787460, 81327708820892342539772865044488, 178405961588244985132285746181186892047941648, 393248, 14965776766290223954537709855993247549719244202049600] ![(.leaf 0 (Common.fact 1240).pointIds 1240), (.leaf 1 (Common.fact 1255).pointIds 1255), (.leaf 2 (Common.fact 1193).pointIds 1193), (.leaf 3 (Common.fact 1203).pointIds 1203), B6901, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1256).pointIds 1256)]
theorem treeEq6900 : B6900.tree = HexagonCover.NBand.M8300_8500.SplitData.node6900 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6901
  · rfl
  · rfl

def B6899 : Block := .branch 173 ![1267650600228229401496703205761, 151153199653077938865666, 53230514994906640848787460, 81327708820892342539772865044488, 178405961588244985132285746181186892047941648, 393248, 2993155353275467248613123706381457052697844809990208] ![(.leaf 0 (Common.fact 1237).pointIds 1237), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6900]
theorem treeEq6899 : B6899.tree = HexagonCover.NBand.M8300_8500.SplitData.node6899 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6900

def B6375 : Block := .branch 109 ![1267651204691139208811290558849, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B6376, (.leaf 5 (Common.fact 211).pointIds 211), B6899]
theorem treeEq6375 : B6375.tree = HexagonCover.NBand.M8300_8500.SplitData.node6375 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6376
  · rfl
  · exact treeEq6899

def B6902 : Block := .branch 148 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 98320, 393248, 2993155353275493832525269947982289904674235078934592] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), Tip6374_6903, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1259).pointIds 1259)]
theorem treeEq6902 : B6902.tree = HexagonCover.NBand.M8300_8500.SplitData.node6902 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6374 : Block := .branch 100 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![B6375, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B6902]
theorem treeEq6374 : B6374.tree = HexagonCover.NBand.M8300_8500.SplitData.node6374 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6375
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6902

theorem accepted6374 : B6374.accepted = true := by decide +kernel
theorem checked6374 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6374 (maskNeeds ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216]) := by
  rw [← treeEq6374]
  exact B6374.sound accepted6374
#print axioms checked6374

def B6948 : Block := .branch 173 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 158456325028528675187087925256, 2854500831259018492916903225796516241337319440, 5709034369502101269473775122669557740833472544, 3741444191567132738249366968347690276612976449945664] ![(.leaf 0 (Common.fact 1309).pointIds 1309), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1277).pointIds 1277), (.leaf 5 (Common.fact 1232).pointIds 1232), (.leaf 6 (Common.fact 1310).pointIds 1310)]
theorem treeEq6948 : B6948.tree = HexagonCover.NBand.M8300_8500.SplitData.node6948 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6947 : Block := .branch 125 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 158456325028528675187087925256, 2854500831259018492916903225796516241337319440, 5709034326966805404356467189747731811862446112, 3741444191588916126644290169672837866716850736857152] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B6948, (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq6947 : B6947.tree = HexagonCover.NBand.M8300_8500.SplitData.node6947 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6948
  · rfl

def B6946 : Block := .branch 97 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2854500831259018492916903225796516241337319440, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B6947, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 1307).pointIds 1307)]
theorem treeEq6946 : B6946.tree = HexagonCover.NBand.M8300_8500.SplitData.node6946 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6947
  · rfl
  · rfl
  · rfl

def B6945 : Block := .branch 120 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2854500829929790497131987352892709181056974864, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B6946, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1306).pointIds 1306)]
theorem treeEq6945 : B6945.tree = HexagonCover.NBand.M8300_8500.SplitData.node6945 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6946
  · rfl
  · rfl

def B6944 : Block := .branch 132 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B6945, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq6944 : B6944.tree = HexagonCover.NBand.M8300_8500.SplitData.node6944 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6945
  · rfl
  · rfl

def B6943 : Block := .branch 142 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B6944, (.leaf 5 (Common.fact 286).pointIds 286), (.leaf 6 (Common.fact 1304).pointIds 1304)]
theorem treeEq6943 : B6943.tree = HexagonCover.NBand.M8300_8500.SplitData.node6943 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6944
  · rfl
  · rfl

def B6942 : Block := .branch 107 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2857282978561736090009263903683071317953839120, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B6943, (.leaf 4 (Common.fact 1303).pointIds 1303), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1287).pointIds 1287)]
theorem treeEq6942 : B6942.tree = HexagonCover.NBand.M8300_8500.SplitData.node6942 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6943
  · rfl
  · rfl
  · rfl

def B6941 : Block := .branch 151 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2787593149816327892691964784081045188345872, 5709034326966805404356467189747731811862446112, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6942, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1302).pointIds 1302)]
theorem treeEq6941 : B6941.tree = HexagonCover.NBand.M8300_8500.SplitData.node6941 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6942
  · rfl
  · rfl

def B6940 : Block := .branch 152 ![374144419156711147060143317779831362839233318355329, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 24584, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 1300).pointIds 1300), B6941, (.leaf 6 (Common.fact 1301).pointIds 1301)]
theorem treeEq6940 : B6940.tree = HexagonCover.NBand.M8300_8500.SplitData.node6940 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6941
  · rfl

def B6939 : Block := .branch 88 ![374144419156711147060143317779831362839233318355329, 618970019644942487019062786, 1461501637330902918203689668419561478172631373828, 24584, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 577).pointIds 577), B6940, (.leaf 2 (Common.fact 1161).pointIds 1161), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1299).pointIds 1299)]
theorem treeEq6939 : B6939.tree = HexagonCover.NBand.M8300_8500.SplitData.node6939 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6940
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6938 : Block := .branch 160 ![374144419156711147060143317779831362839233318355329, 618970019789128043839096322, 4835703278458516698830852, 24584, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), B6939, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), (.leaf 6 (Common.fact 1298).pointIds 1298)]
theorem treeEq6938 : B6938.tree = HexagonCover.NBand.M8300_8500.SplitData.node6938 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6939
  · rfl
  · rfl
  · rfl
  · rfl

def B6937 : Block := .branch 89 ![374144419156711147060143317779831362839233318355329, 146437906389534210, 4835703278458516698830852, 24584, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 3741444202739288725909601740440697003041031489847360] ![(.leaf 0 (Common.fact 1296).pointIds 1296), B6938, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1297).pointIds 1297)]
theorem treeEq6937 : B6937.tree = HexagonCover.NBand.M8300_8500.SplitData.node6937 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6938
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6936 : Block := .branch 168 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 3741444202739288725909601740440697003041031489847360] ![B6937, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1295).pointIds 1295)]
theorem treeEq6936 : B6936.tree = HexagonCover.NBand.M8300_8500.SplitData.node6936 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6937
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6935 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 2787593149816327892691964784081045188345872, 43556142965880123323311949751266331459616, 2993155364425866431789315106089960096977194027843648] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1294).pointIds 1294), (.leaf 5 (Common.fact 589).pointIds 589), B6936]
theorem treeEq6935 : B6935.tree = HexagonCover.NBand.M8300_8500.SplitData.node6935 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6936

def B6934 : Block := .branch 135 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 2787593149816327892691964784081045188345872, 393248, 2993155364425866431789315106089960096977194027843648] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B6935, (.leaf 6 (Common.fact 1293).pointIds 1293)]
theorem treeEq6934 : B6934.tree = HexagonCover.NBand.M8300_8500.SplitData.node6934 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6935
  · rfl

def B6933 : Block := .branch 143 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 2787593149816327892691964784081045188345872, 393248, 2993155353275493832524003535322100960653013274853440] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 798).pointIds 798), (.leaf 5 (Common.fact 217).pointIds 217), B6934]
theorem treeEq6933 : B6933.tree = HexagonCover.NBand.M8300_8500.SplitData.node6933 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6934

def B6932 : Block := .branch 141 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 98320, 393248, 2993155353275493832524003535322100960653013274853440] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), B6933, (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 1292).pointIds 1292)]
theorem treeEq6932 : B6932.tree = HexagonCover.NBand.M8300_8500.SplitData.node6932 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6933
  · rfl
  · rfl

def B6931 : Block := .branch 150 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 98320, 393248, 2993155353275493832524003535322100960653013274853440] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B6932, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1291).pointIds 1291)]
theorem treeEq6931 : B6931.tree = HexagonCover.NBand.M8300_8500.SplitData.node6931 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6932
  · rfl
  · rfl

theorem accepted6931 : B6931.accepted = true := by decide +kernel
theorem checked6931 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6931 (maskNeeds ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 98320, 393248, 2993155353275493832524003535322100960653013274853440]) := by
  rw [← treeEq6931]
  exact B6931.sound accepted6931
#print axioms checked6931

end HexagonCover.NBand.M8300_8500.SplitTree.Run0095
