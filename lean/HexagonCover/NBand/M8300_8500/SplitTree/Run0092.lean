import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0091
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0092
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6621_6623 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6623 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0091.checked6623
def B6655 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq6655 : B6655.tree = HexagonCover.NBand.M8300_8500.SplitData.node6655 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6654 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6655, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq6654 : B6654.tree = HexagonCover.NBand.M8300_8500.SplitData.node6654 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6655
  · rfl
  · rfl

def B6653 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B6654, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6653 : B6653.tree = HexagonCover.NBand.M8300_8500.SplitData.node6653 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6654
  · rfl
  · rfl

def B6652 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6653, (.leaf 0 [] 0)]
theorem treeEq6652 : B6652.tree = HexagonCover.NBand.M8300_8500.SplitData.node6652 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6653
  · rfl

def B6651 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6652, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6651 : B6651.tree = HexagonCover.NBand.M8300_8500.SplitData.node6651 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6652
  · rfl

def B6650 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B6651, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6650 : B6650.tree = HexagonCover.NBand.M8300_8500.SplitData.node6650 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6651
  · rfl
  · rfl

def B6649 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B6650, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq6649 : B6649.tree = HexagonCover.NBand.M8300_8500.SplitData.node6649 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6650
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6648 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6649, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq6648 : B6648.tree = HexagonCover.NBand.M8300_8500.SplitData.node6648 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6649
  · rfl
  · rfl
  · rfl
  · rfl

def B6647 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6648, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq6647 : B6647.tree = HexagonCover.NBand.M8300_8500.SplitData.node6647 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6648
  · rfl
  · rfl
  · rfl

def B6646 : Block := .branch 135 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B6647]
theorem treeEq6646 : B6646.tree = HexagonCover.NBand.M8300_8500.SplitData.node6646 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6647

def B6645 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 649037107316853453566312041250832, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6646, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq6645 : B6645.tree = HexagonCover.NBand.M8300_8500.SplitData.node6645 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6646
  · rfl

def B6622 : Block := .branch 121 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip6621_6623, (.leaf 5 (Common.fact 256).pointIds 256), B6645]
theorem treeEq6622 : B6622.tree = HexagonCover.NBand.M8300_8500.SplitData.node6622 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6645

def B6660 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq6660 : B6660.tree = HexagonCover.NBand.M8300_8500.SplitData.node6660 := by
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

def B6659 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6660, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq6659 : B6659.tree = HexagonCover.NBand.M8300_8500.SplitData.node6659 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6660
  · rfl

def B6658 : Block := .branch 163 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B6659]
theorem treeEq6658 : B6658.tree = HexagonCover.NBand.M8300_8500.SplitData.node6658 := by
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
  · exact treeEq6659

def B6657 : Block := .branch 165 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B6658, (.leaf 0 [] 0)]
theorem treeEq6657 : B6657.tree = HexagonCover.NBand.M8300_8500.SplitData.node6657 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6658
  · rfl

def B6656 : Block := .branch 167 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B6657, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6656 : B6656.tree = HexagonCover.NBand.M8300_8500.SplitData.node6656 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6657
  · rfl

def B6621 : Block := .branch 119 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B6622, B6656, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1075).pointIds 1075)]
theorem treeEq6621 : B6621.tree = HexagonCover.NBand.M8300_8500.SplitData.node6621 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6622
  · exact treeEq6656
  · rfl
  · rfl

theorem accepted6621 : B6621.accepted = true := by decide +kernel
theorem checked6621 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6621 (maskNeeds ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq6621]
  exact B6621.sound accepted6621
#print axioms checked6621

def Tip6620_6674 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6674 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] HexagonCover.NBand.M8300_8500.SplitTree.Run0091.checked6674
def Tip6620_6686 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6686 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] HexagonCover.NBand.M8300_8500.SplitTree.Run0091.checked6686
def Tip6620_6621 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6621 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked6621
def B6673 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq6673 : B6673.tree = HexagonCover.NBand.M8300_8500.SplitData.node6673 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6672 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6673, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq6672 : B6672.tree = HexagonCover.NBand.M8300_8500.SplitData.node6672 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6673
  · rfl
  · rfl

def B6671 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B6672, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6671 : B6671.tree = HexagonCover.NBand.M8300_8500.SplitData.node6671 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6672
  · rfl
  · rfl

def B6670 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B6671, (.leaf 0 [] 0)]
theorem treeEq6670 : B6670.tree = HexagonCover.NBand.M8300_8500.SplitData.node6670 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6671
  · rfl

def B6669 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B6670, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6669 : B6669.tree = HexagonCover.NBand.M8300_8500.SplitData.node6669 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6670
  · rfl

def B6668 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B6669, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6668 : B6668.tree = HexagonCover.NBand.M8300_8500.SplitData.node6668 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6669
  · rfl
  · rfl

def B6667 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B6668, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq6667 : B6667.tree = HexagonCover.NBand.M8300_8500.SplitData.node6667 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6668
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6666 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6667, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq6666 : B6666.tree = HexagonCover.NBand.M8300_8500.SplitData.node6666 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6667
  · rfl
  · rfl
  · rfl
  · rfl

def B6665 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6666, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq6665 : B6665.tree = HexagonCover.NBand.M8300_8500.SplitData.node6665 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6666
  · rfl
  · rfl
  · rfl

def B6664 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 2659105028677148599261180432601939984, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B6665]
theorem treeEq6664 : B6664.tree = HexagonCover.NBand.M8300_8500.SplitData.node6664 := by
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
  · exact treeEq6665

def B6663 : Block := .branch 125 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B6664, Tip6620_6674]
theorem treeEq6663 : B6663.tree = HexagonCover.NBand.M8300_8500.SplitData.node6663 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6664
  · rfl

def B6662 : Block := .branch 121 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B6663, (.leaf 5 (Common.fact 256).pointIds 256), Tip6620_6686]
theorem treeEq6662 : B6662.tree = HexagonCover.NBand.M8300_8500.SplitData.node6662 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6663
  · rfl
  · rfl

def B6702 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq6702 : B6702.tree = HexagonCover.NBand.M8300_8500.SplitData.node6702 := by
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

def B6701 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6702, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq6701 : B6701.tree = HexagonCover.NBand.M8300_8500.SplitData.node6701 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6702
  · rfl

def B6700 : Block := .branch 163 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B6701]
theorem treeEq6700 : B6700.tree = HexagonCover.NBand.M8300_8500.SplitData.node6700 := by
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
  · exact treeEq6701

def B6699 : Block := .branch 165 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B6700, (.leaf 0 [] 0)]
theorem treeEq6699 : B6699.tree = HexagonCover.NBand.M8300_8500.SplitData.node6699 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6700
  · rfl

def B6698 : Block := .branch 167 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B6699, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6698 : B6698.tree = HexagonCover.NBand.M8300_8500.SplitData.node6698 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6699
  · rfl

def B6661 : Block := .branch 119 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B6662, B6698, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1075).pointIds 1075)]
theorem treeEq6661 : B6661.tree = HexagonCover.NBand.M8300_8500.SplitData.node6661 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6662
  · exact treeEq6698
  · rfl
  · rfl

def B6620 : Block := .branch 115 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip6620_6621, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B6661, (.leaf 0 [] 0)]
theorem treeEq6620 : B6620.tree = HexagonCover.NBand.M8300_8500.SplitData.node6620 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6661
  · rfl

theorem accepted6620 : B6620.accepted = true := by decide +kernel
theorem checked6620 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6620 (maskNeeds ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq6620]
  exact B6620.sound accepted6620
#print axioms checked6620

def Tip6618_6620 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6620 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked6620
def B6713 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq6713 : B6713.tree = HexagonCover.NBand.M8300_8500.SplitData.node6713 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6712 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6713, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq6712 : B6712.tree = HexagonCover.NBand.M8300_8500.SplitData.node6712 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6713
  · rfl
  · rfl

def B6711 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6712, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6711 : B6711.tree = HexagonCover.NBand.M8300_8500.SplitData.node6711 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6712
  · rfl
  · rfl

def B6710 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6711, (.leaf 0 [] 0)]
theorem treeEq6710 : B6710.tree = HexagonCover.NBand.M8300_8500.SplitData.node6710 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6711
  · rfl

def B6709 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6710, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6709 : B6709.tree = HexagonCover.NBand.M8300_8500.SplitData.node6709 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6710
  · rfl

def B6708 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6709, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6708 : B6708.tree = HexagonCover.NBand.M8300_8500.SplitData.node6708 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6709
  · rfl
  · rfl

def B6707 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B6708, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq6707 : B6707.tree = HexagonCover.NBand.M8300_8500.SplitData.node6707 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6708
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6706 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6707, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq6706 : B6706.tree = HexagonCover.NBand.M8300_8500.SplitData.node6706 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6707
  · rfl
  · rfl
  · rfl
  · rfl

def B6705 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6706, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq6705 : B6705.tree = HexagonCover.NBand.M8300_8500.SplitData.node6705 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6706
  · rfl
  · rfl
  · rfl

def B6704 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B6705]
theorem treeEq6704 : B6704.tree = HexagonCover.NBand.M8300_8500.SplitData.node6704 := by
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
  · exact treeEq6705

def B6703 : Block := .branch 135 ![385, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B6704, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq6703 : B6703.tree = HexagonCover.NBand.M8300_8500.SplitData.node6703 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6704
  · rfl

def B6619 : Block := .branch 113 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip6618_6620, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B6703]
theorem treeEq6619 : B6619.tree = HexagonCover.NBand.M8300_8500.SplitData.node6619 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6703

def B6718 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq6718 : B6718.tree = HexagonCover.NBand.M8300_8500.SplitData.node6718 := by
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

def B6717 : Block := .branch 169 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6718, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq6717 : B6717.tree = HexagonCover.NBand.M8300_8500.SplitData.node6717 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6718
  · rfl

def B6716 : Block := .branch 163 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 973555660975280180349468061827088, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B6717]
theorem treeEq6716 : B6716.tree = HexagonCover.NBand.M8300_8500.SplitData.node6716 := by
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
  · exact treeEq6717

def B6715 : Block := .branch 165 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 973555660975280180349468061827088, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B6716, (.leaf 0 [] 0)]
theorem treeEq6715 : B6715.tree = HexagonCover.NBand.M8300_8500.SplitData.node6715 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6716
  · rfl

def B6714 : Block := .branch 167 ![604462909807314587353473, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 973555660975280180349468061827088, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B6715, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6714 : B6714.tree = HexagonCover.NBand.M8300_8500.SplitData.node6714 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6715
  · rfl

def B6618 : Block := .branch 108 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B6619, B6714, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1074).pointIds 1074)]
theorem treeEq6618 : B6618.tree = HexagonCover.NBand.M8300_8500.SplitData.node6618 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6619
  · exact treeEq6714
  · rfl
  · rfl

theorem accepted6618 : B6618.accepted = true := by decide +kernel
theorem checked6618 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6618 (maskNeeds ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq6618]
  exact B6618.sound accepted6618
#print axioms checked6618

def B6759 : Block := .branch 173 ![6360455125664089546754375769394940587718582093218177, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1099).pointIds 1099), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1102).pointIds 1102), (.leaf 4 (Common.fact 1103).pointIds 1103), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6759 : B6759.tree = HexagonCover.NBand.M8300_8500.SplitData.node6759 := by
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

def B6758 : Block := .branch 172 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![B6759, (.leaf 1 (Common.fact 1093).pointIds 1093), (.leaf 2 (Common.fact 1094).pointIds 1094), (.leaf 3 (Common.fact 1095).pointIds 1095), (.leaf 4 (Common.fact 1096).pointIds 1096), (.leaf 5 (Common.fact 1097).pointIds 1097), (.leaf 6 (Common.fact 1098).pointIds 1098)]
theorem treeEq6758 : B6758.tree = HexagonCover.NBand.M8300_8500.SplitData.node6758 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6759
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6760 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429937849850465379425745953950848278536, 52614058943912505055332653977786188707613571645456, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1107).pointIds 1107), (.leaf 4 (Common.fact 1108).pointIds 1108), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6760 : B6760.tree = HexagonCover.NBand.M8300_8500.SplitData.node6760 := by
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

def B6761 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5708990813359135389350451810719806474502406176, 3747290198116456349922180469738516123311325280993344] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1107).pointIds 1107), (.leaf 4 (Common.fact 1103).pointIds 1103), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1109).pointIds 1109)]
theorem treeEq6761 : B6761.tree = HexagonCover.NBand.M8300_8500.SplitData.node6761 := by
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

def B6757 : Block := .branch 162 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), B6758, B6760, (.leaf 5 (Common.fact 358).pointIds 358), B6761]
theorem treeEq6757 : B6757.tree = HexagonCover.NBand.M8300_8500.SplitData.node6757 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6758
  · exact treeEq6760
  · rfl
  · exact treeEq6761

def B6762 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 46773761385402252517907265098731776435464343781408, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1107).pointIds 1107), (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 1111).pointIds 1111), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6762 : B6762.tree = HexagonCover.NBand.M8300_8500.SplitData.node6762 := by
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

def B6756 : Block := .branch 165 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B6757, B6762, (.leaf 0 [] 0)]
theorem treeEq6756 : B6756.tree = HexagonCover.NBand.M8300_8500.SplitData.node6756 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6757
  · exact treeEq6762
  · rfl

def B6763 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429938174210562712823944061919780954120, 12057388507979949075180399869909334912161443577872, 5708990813359135389350451810719806474502406176, 3741444191567132738249682643057708048583075726622784] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1113).pointIds 1113)]
theorem treeEq6763 : B6763.tree = HexagonCover.NBand.M8300_8500.SplitData.node6763 := by
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

def B6755 : Block := .branch 98 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429938174210562712823944061919780954120, 12057388507979949075180399869909334912161443577872, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B6756, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B6763]
theorem treeEq6755 : B6755.tree = HexagonCover.NBand.M8300_8500.SplitData.node6755 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6756
  · rfl
  · rfl
  · exact treeEq6763

def B6764 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429938174210562712823944061919780954120, 365375409332726378588028525032524321226024386576, 5708990813359135389350451810719806474502406176, 5249713881292624549835568477770855067517623935172672] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1101).pointIds 1101), (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 1114).pointIds 1114), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1115).pointIds 1115)]
theorem treeEq6764 : B6764.tree = HexagonCover.NBand.M8300_8500.SplitData.node6764 := by
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

def B6754 : Block := .branch 163 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 4384504911992708754611059333852127517484496459780, 89551429938174210562712823944061919780954120, 365375409332726378588028525032524321226024386576, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6755, (.leaf 5 (Common.fact 329).pointIds 329), B6764]
theorem treeEq6754 : B6754.tree = HexagonCover.NBand.M8300_8500.SplitData.node6754 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6755
  · rfl
  · exact treeEq6764

def B6765 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 2923092477642599958899935808305656632757889032200, 365375409332726378588028525032524321226024386576, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1117).pointIds 1117), (.leaf 4 (Common.fact 1114).pointIds 1114), (.leaf 5 (Common.fact 1104).pointIds 1104), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6765 : B6765.tree = HexagonCover.NBand.M8300_8500.SplitData.node6765 := by
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

def B6753 : Block := .branch 161 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 89551429938174210562712823944061919780954120, 365375409332726378588028525032524321226024386576, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6754, B6765, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1092).pointIds 1092)]
theorem treeEq6753 : B6753.tree = HexagonCover.NBand.M8300_8500.SplitData.node6753 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6754
  · exact treeEq6765
  · rfl
  · rfl
  · rfl

def B6766 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 89551429938174210562712823944061919780954120, 2854495385412568799223888792352556584806744080, 365375409375261025416038516111992580842954555424, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1112).pointIds 1112), (.leaf 4 (Common.fact 1118).pointIds 1118), (.leaf 5 (Common.fact 1119).pointIds 1119), (.leaf 6 (Common.fact 1105).pointIds 1105)]
theorem treeEq6766 : B6766.tree = HexagonCover.NBand.M8300_8500.SplitData.node6766 := by
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

def B6752 : Block := .branch 158 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 89551429938174210562712823944061919780954120, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), B6753, B6766, (.leaf 0 [] 0)]
theorem treeEq6752 : B6752.tree = HexagonCover.NBand.M8300_8500.SplitData.node6752 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6753
  · exact treeEq6766
  · rfl

def B6770 : Block := .branch 173 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2943698366206691291790031665443150030830665744, 233845970963757826047978923686416002951423709282336, 5249713881292624549835568477770855067517623935172672] ![(.leaf 0 (Common.fact 1106).pointIds 1106), (.leaf 1 (Common.fact 1100).pointIds 1100), (.leaf 2 (Common.fact 1116).pointIds 1116), (.leaf 3 (Common.fact 1122).pointIds 1122), (.leaf 4 (Common.fact 1123).pointIds 1123), (.leaf 5 (Common.fact 1124).pointIds 1124), (.leaf 6 (Common.fact 1115).pointIds 1115)]
theorem treeEq6770 : B6770.tree = HexagonCover.NBand.M8300_8500.SplitData.node6770 := by
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

def B6769 : Block := .branch 163 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2943698366206691291790031665443150030830665744, 233845970963757826047978923686416002951423709282336, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1086).pointIds 1086), (.leaf 5 (Common.fact 329).pointIds 329), B6770]
theorem treeEq6769 : B6769.tree = HexagonCover.NBand.M8300_8500.SplitData.node6769 := by
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
  · exact treeEq6770

def B6768 : Block := .branch 165 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2943698366206691291790031665443150030830665744, 187077918569168932665461009039494946322433867907104, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1121).pointIds 1121), B6769, (.leaf 0 [] 0)]
theorem treeEq6768 : B6768.tree = HexagonCover.NBand.M8300_8500.SplitData.node6768 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6769
  · rfl

def B6767 : Block := .branch 167 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2943698366206691291790031665443150030830665744, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1120).pointIds 1120), B6768, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6767 : B6767.tree = HexagonCover.NBand.M8300_8500.SplitData.node6767 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6768
  · rfl

def B6751 : Block := .branch 146 ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), B6752, B6767, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6751 : B6751.tree = HexagonCover.NBand.M8300_8500.SplitData.node6751 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6752
  · exact treeEq6767
  · rfl
  · rfl

theorem accepted6751 : B6751.accepted = true := by decide +kernel
theorem checked6751 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6751 (maskNeeds ![374144419156711193792082694589045339207882397188481, 928455029466287555743843842, 1461501637330902918203689668419561478172631373828, 348449144051717996569950853468473757032456, 2854495385412568799223888792352556584806744080, 5708990813359135389350451810719806474502406176, 5238021868193977326489938999109124803360376474828864]) := by
  rw [← treeEq6751]
  exact B6751.sound accepted6751
#print axioms checked6751

end HexagonCover.NBand.M8300_8500.SplitTree.Run0092
