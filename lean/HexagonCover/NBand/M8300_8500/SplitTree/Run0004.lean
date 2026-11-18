import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0294_0296 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0296 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0003.checked0296
def B0328 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M8300_8500.SplitData.node0328 := by
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

def B0327 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0328, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M8300_8500.SplitData.node0327 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0328
  · rfl
  · rfl

def B0326 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0327, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M8300_8500.SplitData.node0326 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0327
  · rfl
  · rfl

def B0325 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0326, (.leaf 0 [] 0)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M8300_8500.SplitData.node0325 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0326
  · rfl

def B0324 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0325, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M8300_8500.SplitData.node0324 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0325
  · rfl

def B0323 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0324, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M8300_8500.SplitData.node0323 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · rfl

def B0322 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 577).pointIds 577), B0323, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M8300_8500.SplitData.node0322 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0323
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0321 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0322, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M8300_8500.SplitData.node0321 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0322
  · rfl
  · rfl
  · rfl
  · rfl

def B0320 : Block := .branch 170 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0321, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M8300_8500.SplitData.node0320 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · rfl
  · rfl

def B0319 : Block := .branch 135 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0320]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M8300_8500.SplitData.node0319 := by
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
  · exact treeEq0320

def B0318 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0319, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M8300_8500.SplitData.node0318 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0319
  · rfl

def B0295 : Block := .branch 121 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip0294_0296, (.leaf 5 (Common.fact 256).pointIds 256), B0318]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M8300_8500.SplitData.node0295 := by
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
  · exact treeEq0318

def B0333 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M8300_8500.SplitData.node0333 := by
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

def B0332 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0333, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M8300_8500.SplitData.node0332 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0333
  · rfl

def B0331 : Block := .branch 163 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0332]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M8300_8500.SplitData.node0331 := by
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
  · exact treeEq0332

def B0330 : Block := .branch 165 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0331, (.leaf 0 [] 0)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M8300_8500.SplitData.node0330 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0331
  · rfl

def B0329 : Block := .branch 167 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0330, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M8300_8500.SplitData.node0329 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl

def B0294 : Block := .branch 119 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0295, B0329, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M8300_8500.SplitData.node0294 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0295
  · exact treeEq0329
  · rfl
  · rfl

theorem accepted0294 : B0294.accepted = true := by decide +kernel
theorem checked0294 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0294 (maskNeeds ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0294]
  exact B0294.sound accepted0294
#print axioms checked0294

def Tip0293_0347 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0347 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582620114145322302633222186454766830747712] HexagonCover.NBand.M8300_8500.SplitTree.Run0003.checked0347
def Tip0293_0359 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0359 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] HexagonCover.NBand.M8300_8500.SplitTree.Run0003.checked0359
def Tip0293_0294 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0294 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0294
def B0346 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M8300_8500.SplitData.node0346 := by
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

def B0345 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0346, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M8300_8500.SplitData.node0345 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0346
  · rfl
  · rfl

def B0344 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0345, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M8300_8500.SplitData.node0344 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl
  · rfl

def B0343 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0344, (.leaf 0 [] 0)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M8300_8500.SplitData.node0343 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl

def B0342 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0343, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M8300_8500.SplitData.node0342 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0343
  · rfl

def B0341 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0342, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M8300_8500.SplitData.node0341 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl

def B0340 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 577).pointIds 577), B0341, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M8300_8500.SplitData.node0340 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0341
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0339 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0340, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M8300_8500.SplitData.node0339 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0340
  · rfl
  · rfl
  · rfl
  · rfl

def B0338 : Block := .branch 170 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0339, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M8300_8500.SplitData.node0338 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0339
  · rfl
  · rfl
  · rfl

def B0337 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B0338]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M8300_8500.SplitData.node0337 := by
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
  · exact treeEq0338

def B0336 : Block := .branch 125 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0337, Tip0293_0347]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M8300_8500.SplitData.node0336 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl

def B0335 : Block := .branch 121 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0336, (.leaf 5 (Common.fact 256).pointIds 256), Tip0293_0359]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M8300_8500.SplitData.node0335 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336
  · rfl
  · rfl

def B0375 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M8300_8500.SplitData.node0375 := by
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

def B0374 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0375, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M8300_8500.SplitData.node0374 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375
  · rfl

def B0373 : Block := .branch 163 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0374]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M8300_8500.SplitData.node0373 := by
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
  · exact treeEq0374

def B0372 : Block := .branch 165 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0373, (.leaf 0 [] 0)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M8300_8500.SplitData.node0372 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl

def B0371 : Block := .branch 167 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0372, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M8300_8500.SplitData.node0371 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0372
  · rfl

def B0334 : Block := .branch 119 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0335, B0371, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M8300_8500.SplitData.node0334 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · exact treeEq0371
  · rfl
  · rfl

def B0293 : Block := .branch 115 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0293_0294, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B0334, (.leaf 0 [] 0)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M8300_8500.SplitData.node0293 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl

theorem accepted0293 : B0293.accepted = true := by decide +kernel
theorem checked0293 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0293 (maskNeeds ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0293]
  exact B0293.sound accepted0293
#print axioms checked0293

def Tip0291_0293 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0293 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0293
def B0386 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M8300_8500.SplitData.node0386 := by
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

def B0385 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0386, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M8300_8500.SplitData.node0385 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl
  · rfl

def B0384 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0385, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M8300_8500.SplitData.node0384 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0385
  · rfl
  · rfl

def B0383 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0384, (.leaf 0 [] 0)]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M8300_8500.SplitData.node0383 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0384
  · rfl

def B0382 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0383, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M8300_8500.SplitData.node0382 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0383
  · rfl

def B0381 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0382, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M8300_8500.SplitData.node0381 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl
  · rfl

def B0380 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B0381, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M8300_8500.SplitData.node0380 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0381
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0379 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0380, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M8300_8500.SplitData.node0379 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0380
  · rfl
  · rfl
  · rfl
  · rfl

def B0378 : Block := .branch 170 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0379, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M8300_8500.SplitData.node0378 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0379
  · rfl
  · rfl
  · rfl

def B0377 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B0378]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M8300_8500.SplitData.node0377 := by
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
  · exact treeEq0378

def B0376 : Block := .branch 135 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0377, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M8300_8500.SplitData.node0376 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl

def B0292 : Block := .branch 113 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0291_0293, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0376]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M8300_8500.SplitData.node0292 := by
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
  · exact treeEq0376

def B0391 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M8300_8500.SplitData.node0391 := by
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

def B0390 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0391, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M8300_8500.SplitData.node0390 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0391
  · rfl

def B0389 : Block := .branch 163 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B0390]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M8300_8500.SplitData.node0389 := by
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
  · exact treeEq0390

def B0388 : Block := .branch 165 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B0389, (.leaf 0 [] 0)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M8300_8500.SplitData.node0388 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl

def B0387 : Block := .branch 167 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B0388, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M8300_8500.SplitData.node0387 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388
  · rfl

def B0291 : Block := .branch 108 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0292, B0387, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M8300_8500.SplitData.node0291 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0292
  · exact treeEq0387
  · rfl
  · rfl

theorem accepted0291 : B0291.accepted = true := by decide +kernel
theorem checked0291 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0291 (maskNeeds ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0291]
  exact B0291.sound accepted0291
#print axioms checked0291

def Tip0044_0045 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0045 ![15578158226506943148609195101651329, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] HexagonCover.NBand.M8300_8500.SplitTree.Run0003.checked0045
def B0286 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M8300_8500.SplitData.node0286 := by
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

def B0285 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0286, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M8300_8500.SplitData.node0285 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · rfl

def B0284 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0285, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M8300_8500.SplitData.node0284 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285
  · rfl
  · rfl

def B0283 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0284, (.leaf 0 [] 0)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M8300_8500.SplitData.node0283 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0284
  · rfl

def B0282 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0283, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M8300_8500.SplitData.node0282 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl

def B0281 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0282, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M8300_8500.SplitData.node0281 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl
  · rfl

def B0280 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B0281, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M8300_8500.SplitData.node0280 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0281
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0279 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0280, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M8300_8500.SplitData.node0279 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0280
  · rfl
  · rfl
  · rfl
  · rfl

def B0278 : Block := .branch 170 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 656).pointIds 656), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), B0279, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M8300_8500.SplitData.node0278 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0279
  · rfl
  · rfl
  · rfl

def B0277 : Block := .branch 169 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 655).pointIds 655), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B0278]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M8300_8500.SplitData.node0277 := by
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
  · exact treeEq0278

def B0276 : Block := .branch 135 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0277, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M8300_8500.SplitData.node0276 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0277
  · rfl

def B0275 : Block := .branch 171 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888412752904364991996897434480670146624] ![(.leaf 0 (Common.fact 653).pointIds 653), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 563).pointIds 563), B0276]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M8300_8500.SplitData.node0275 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276

def B0274 : Block := .branch 168 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177265692761047816628444402561939144768] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 561).pointIds 561), B0275]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M8300_8500.SplitData.node0274 := by
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
  · exact treeEq0275

def B0044 : Block := .branch 113 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![Tip0044_0045, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0274]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M8300_8500.SplitData.node0044 := by
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
  · exact treeEq0274

theorem accepted0044 : B0044.accepted = true := by decide +kernel
theorem checked0044 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0044 (maskNeeds ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576]) := by
  rw [← treeEq0044]
  exact B0044.sound accepted0044
#print axioms checked0044

def B0430 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M8300_8500.SplitData.node0430 := by
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

def B0429 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0430, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M8300_8500.SplitData.node0429 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0430
  · rfl
  · rfl

def B0428 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B0429, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M8300_8500.SplitData.node0428 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0429
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0427 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0428, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M8300_8500.SplitData.node0427 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0428
  · rfl
  · rfl
  · rfl
  · rfl

def B0426 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B0427]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M8300_8500.SplitData.node0426 := by
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
  · exact treeEq0427

def B0425 : Block := .branch 169 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89551429938498570660046222142169888713703440, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 675).pointIds 675), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0426, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M8300_8500.SplitData.node0425 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0426
  · rfl

def B0424 : Block := .branch 138 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202980794771529673459726544159758065172496, 233840261972944466912589573234605283144949207269408, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B0425, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M8300_8500.SplitData.node0424 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0425
  · rfl
  · rfl

def B0423 : Block := .branch 165 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 187072209578355573530071658587684226515959365894176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B0424, (.leaf 0 [] 0)]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M8300_8500.SplitData.node0423 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0424
  · rfl

def B0422 : Block := .branch 167 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B0423, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M8300_8500.SplitData.node0422 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0423
  · rfl

def B0421 : Block := .branch 146 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 1496577676626845252854729617484438792706392152104968, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B0422, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M8300_8500.SplitData.node0421 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0422
  · rfl
  · rfl

def B0420 : Block := .branch 170 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 677).pointIds 677), (.leaf 2 (Common.fact 430).pointIds 430), B0421, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M8300_8500.SplitData.node0420 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0421
  · rfl
  · rfl
  · rfl

theorem accepted0420 : B0420.accepted = true := by decide +kernel
theorem checked0420 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0420 (maskNeeds ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 664614156348782964980578717228097544, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq0420]
  exact B0420.sound accepted0420
#print axioms checked0420

end HexagonCover.NBand.M8300_8500.SplitTree.Run0004
