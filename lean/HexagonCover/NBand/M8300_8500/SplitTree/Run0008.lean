import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0594_0596 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0596 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0007.checked0596
def B0628 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M8300_8500.SplitData.node0628 := by
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

def B0627 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0628, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M8300_8500.SplitData.node0627 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0628
  · rfl
  · rfl

def B0626 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0627, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M8300_8500.SplitData.node0626 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0627
  · rfl
  · rfl

def B0625 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0626, (.leaf 0 [] 0)]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M8300_8500.SplitData.node0625 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0626
  · rfl

def B0624 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0625, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M8300_8500.SplitData.node0624 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0625
  · rfl

def B0623 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0624, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M8300_8500.SplitData.node0623 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0624
  · rfl
  · rfl

def B0622 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B0623, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M8300_8500.SplitData.node0622 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0623
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0621 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0622, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M8300_8500.SplitData.node0621 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0622
  · rfl
  · rfl
  · rfl
  · rfl

def B0620 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0621, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M8300_8500.SplitData.node0620 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl
  · rfl
  · rfl

def B0619 : Block := .branch 135 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0620]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M8300_8500.SplitData.node0619 := by
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
  · exact treeEq0620

def B0618 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0619, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M8300_8500.SplitData.node0618 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0619
  · rfl

def B0595 : Block := .branch 121 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip0594_0596, (.leaf 5 (Common.fact 256).pointIds 256), B0618]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M8300_8500.SplitData.node0595 := by
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
  · exact treeEq0618

def B0633 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M8300_8500.SplitData.node0633 := by
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

def B0632 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0633, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M8300_8500.SplitData.node0632 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0633
  · rfl

def B0631 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0632]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M8300_8500.SplitData.node0631 := by
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
  · exact treeEq0632

def B0630 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0631, (.leaf 0 [] 0)]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M8300_8500.SplitData.node0630 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0631
  · rfl

def B0629 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0630, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M8300_8500.SplitData.node0629 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0630
  · rfl

def B0594 : Block := .branch 119 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0595, B0629, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M8300_8500.SplitData.node0594 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0595
  · exact treeEq0629
  · rfl
  · rfl

theorem accepted0594 : B0594.accepted = true := by decide +kernel
theorem checked0594 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0594 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0594]
  exact B0594.sound accepted0594
#print axioms checked0594

def Tip0593_0647 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0647 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] HexagonCover.NBand.M8300_8500.SplitTree.Run0007.checked0647
def Tip0593_0659 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0659 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] HexagonCover.NBand.M8300_8500.SplitTree.Run0007.checked0659
def Tip0593_0594 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0594 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0594
def B0646 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M8300_8500.SplitData.node0646 := by
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

def B0645 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0646, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M8300_8500.SplitData.node0645 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0646
  · rfl
  · rfl

def B0644 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0645, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M8300_8500.SplitData.node0644 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0645
  · rfl
  · rfl

def B0643 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0644, (.leaf 0 [] 0)]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M8300_8500.SplitData.node0643 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0644
  · rfl

def B0642 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0643, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M8300_8500.SplitData.node0642 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0643
  · rfl

def B0641 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0642, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M8300_8500.SplitData.node0641 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0642
  · rfl
  · rfl

def B0640 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B0641, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M8300_8500.SplitData.node0640 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0641
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0639 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0640, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M8300_8500.SplitData.node0639 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0640
  · rfl
  · rfl
  · rfl
  · rfl

def B0638 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0639, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M8300_8500.SplitData.node0638 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0639
  · rfl
  · rfl
  · rfl

def B0637 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B0638]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M8300_8500.SplitData.node0637 := by
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
  · exact treeEq0638

def B0636 : Block := .branch 125 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0637, Tip0593_0647]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M8300_8500.SplitData.node0636 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0637
  · rfl

def B0635 : Block := .branch 121 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0636, (.leaf 5 (Common.fact 256).pointIds 256), Tip0593_0659]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M8300_8500.SplitData.node0635 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0636
  · rfl
  · rfl

def B0675 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M8300_8500.SplitData.node0675 := by
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

def B0674 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0675, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M8300_8500.SplitData.node0674 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0675
  · rfl

def B0673 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0674]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M8300_8500.SplitData.node0673 := by
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
  · exact treeEq0674

def B0672 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0673, (.leaf 0 [] 0)]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M8300_8500.SplitData.node0672 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0673
  · rfl

def B0671 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0672, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M8300_8500.SplitData.node0671 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0672
  · rfl

def B0634 : Block := .branch 119 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0635, B0671, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M8300_8500.SplitData.node0634 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0635
  · exact treeEq0671
  · rfl
  · rfl

def B0593 : Block := .branch 115 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0593_0594, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B0634, (.leaf 0 [] 0)]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M8300_8500.SplitData.node0593 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0634
  · rfl

theorem accepted0593 : B0593.accepted = true := by decide +kernel
theorem checked0593 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0593 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0593]
  exact B0593.sound accepted0593
#print axioms checked0593

def Tip0591_0593 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0593 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0593
def B0686 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M8300_8500.SplitData.node0686 := by
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

def B0685 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0686, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M8300_8500.SplitData.node0685 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0686
  · rfl
  · rfl

def B0684 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0685, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M8300_8500.SplitData.node0684 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0685
  · rfl
  · rfl

def B0683 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0684, (.leaf 0 [] 0)]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M8300_8500.SplitData.node0683 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0684
  · rfl

def B0682 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0683, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M8300_8500.SplitData.node0682 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0683
  · rfl

def B0681 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0682, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M8300_8500.SplitData.node0681 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0682
  · rfl
  · rfl

def B0680 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B0681, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M8300_8500.SplitData.node0680 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0681
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0679 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0680, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M8300_8500.SplitData.node0679 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0680
  · rfl
  · rfl
  · rfl
  · rfl

def B0678 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0679, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M8300_8500.SplitData.node0678 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl
  · rfl
  · rfl

def B0677 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B0678]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M8300_8500.SplitData.node0677 := by
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
  · exact treeEq0678

def B0676 : Block := .branch 135 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0677, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M8300_8500.SplitData.node0676 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0677
  · rfl

def B0592 : Block := .branch 113 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0591_0593, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0676]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M8300_8500.SplitData.node0592 := by
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
  · exact treeEq0676

def B0691 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M8300_8500.SplitData.node0691 := by
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

def B0690 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0691, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M8300_8500.SplitData.node0690 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0691
  · rfl

def B0689 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B0690]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M8300_8500.SplitData.node0689 := by
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
  · exact treeEq0690

def B0688 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B0689, (.leaf 0 [] 0)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M8300_8500.SplitData.node0688 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0689
  · rfl

def B0687 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B0688, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M8300_8500.SplitData.node0687 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0688
  · rfl

def B0591 : Block := .branch 108 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0592, B0687, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M8300_8500.SplitData.node0591 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0592
  · exact treeEq0687
  · rfl
  · rfl

theorem accepted0591 : B0591.accepted = true := by decide +kernel
theorem checked0591 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0591 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0591]
  exact B0591.sound accepted0591
#print axioms checked0591

def B0728 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M8300_8500.SplitData.node0728 := by
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

def B0727 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0728, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M8300_8500.SplitData.node0727 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0728
  · rfl
  · rfl

def B0726 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B0727, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M8300_8500.SplitData.node0726 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0727
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0725 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0726, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M8300_8500.SplitData.node0725 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0726
  · rfl
  · rfl
  · rfl
  · rfl

def B0724 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B0725]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M8300_8500.SplitData.node0724 := by
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
  · exact treeEq0725

def B0723 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551429938498570660046222142169888713703440, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0724, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M8300_8500.SplitData.node0723 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0724
  · rfl

def B0722 : Block := .branch 138 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 233840261972944466912589573234605283144949207269408, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0723, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M8300_8500.SplitData.node0722 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0721 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 187072209578355573530071658587684226515959365894176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0722, (.leaf 0 [] 0)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M8300_8500.SplitData.node0721 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0722
  · rfl

def B0720 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0721, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M8300_8500.SplitData.node0720 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0721
  · rfl

def B0719 : Block := .branch 146 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0720, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M8300_8500.SplitData.node0719 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0720
  · rfl
  · rfl

def B0718 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0719, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M8300_8500.SplitData.node0718 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0719
  · rfl
  · rfl
  · rfl

theorem accepted0718 : B0718.accepted = true := by decide +kernel
theorem checked0718 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0718 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq0718]
  exact B0718.sound accepted0718
#print axioms checked0718

def Tip0707_0718 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0718 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] checked0718
def B0717 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M8300_8500.SplitData.node0717 := by
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

def B0716 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0717, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M8300_8500.SplitData.node0716 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0717
  · rfl
  · rfl

def B0715 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0716, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M8300_8500.SplitData.node0715 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0716
  · rfl
  · rfl

def B0714 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0715, (.leaf 0 [] 0)]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M8300_8500.SplitData.node0714 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0715
  · rfl

def B0713 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0714, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M8300_8500.SplitData.node0713 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0714
  · rfl

def B0712 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0713, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M8300_8500.SplitData.node0712 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0713
  · rfl
  · rfl

def B0711 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B0712, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M8300_8500.SplitData.node0711 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0710 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0711, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M8300_8500.SplitData.node0710 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0711
  · rfl
  · rfl
  · rfl
  · rfl

def B0709 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0710, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M8300_8500.SplitData.node0709 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0710
  · rfl
  · rfl
  · rfl

def B0708 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 42535295865117307932921825928971419680, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 540).pointIds 540), B0709]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M8300_8500.SplitData.node0708 := by
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
  · exact treeEq0709

def B0707 : Block := .branch 125 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0708, Tip0707_0718]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M8300_8500.SplitData.node0707 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0708
  · rfl

theorem accepted0707 : B0707.accepted = true := by decide +kernel
theorem checked0707 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0707 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0707]
  exact B0707.sound accepted0707
#print axioms checked0707

end HexagonCover.NBand.M8300_8500.SplitTree.Run0008
