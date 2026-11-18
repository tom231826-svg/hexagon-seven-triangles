import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0004
import HexagonCover.NBand.M8300_8500.SplitTree.Run0005
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0404_0406 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0406 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0005.checked0406
def B0499 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M8300_8500.SplitData.node0499 := by
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

def B0498 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0499, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M8300_8500.SplitData.node0498 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0499
  · rfl
  · rfl

def B0497 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0498, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M8300_8500.SplitData.node0497 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0498
  · rfl
  · rfl

def B0496 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0497, (.leaf 0 [] 0)]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M8300_8500.SplitData.node0496 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0497
  · rfl

def B0495 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0496, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M8300_8500.SplitData.node0495 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0496
  · rfl

def B0494 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0495, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M8300_8500.SplitData.node0494 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0495
  · rfl
  · rfl

def B0493 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 577).pointIds 577), B0494, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M8300_8500.SplitData.node0493 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0494
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0492 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0493, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M8300_8500.SplitData.node0492 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0493
  · rfl
  · rfl
  · rfl
  · rfl

def B0491 : Block := .branch 170 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 24584, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 677).pointIds 677), (.leaf 2 (Common.fact 430).pointIds 430), B0492, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M8300_8500.SplitData.node0491 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0492
  · rfl
  · rfl
  · rfl

def B0490 : Block := .branch 169 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 675).pointIds 675), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B0491]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M8300_8500.SplitData.node0490 := by
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
  · exact treeEq0491

def B0489 : Block := .branch 135 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0490, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M8300_8500.SplitData.node0489 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0490
  · rfl

def B0405 : Block := .branch 113 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0404_0406, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0489]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M8300_8500.SplitData.node0405 := by
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
  · exact treeEq0489

def B0504 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M8300_8500.SplitData.node0504 := by
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

def B0503 : Block := .branch 169 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 675).pointIds 675), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0504, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M8300_8500.SplitData.node0503 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0504
  · rfl

def B0502 : Block := .branch 163 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B0503]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M8300_8500.SplitData.node0502 := by
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
  · exact treeEq0503

def B0501 : Block := .branch 165 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B0502, (.leaf 0 [] 0)]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M8300_8500.SplitData.node0501 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0502
  · rfl

def B0500 : Block := .branch 167 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 973555660975280180349468061827088, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B0501, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M8300_8500.SplitData.node0500 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl

def B0404 : Block := .branch 108 ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0405, B0500, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M8300_8500.SplitData.node0404 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0405
  · exact treeEq0500
  · rfl
  · rfl

theorem accepted0404 : B0404.accepted = true := by decide +kernel
theorem checked0404 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0404 (maskNeeds ![1267650600523956019228173140353, 377789318630121372911106, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0404]
  exact B0404.sound accepted0404
#print axioms checked0404

def Tip0043_0291 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0291 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0004.checked0291
def Tip0043_0044 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0044 ![5193564509437287891548202443211137, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] HexagonCover.NBand.M8300_8500.SplitTree.Run0004.checked0044
def B0396 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M8300_8500.SplitData.node0396 := by
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

def B0395 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0396, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M8300_8500.SplitData.node0395 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0396
  · rfl

def B0394 : Block := .branch 163 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B0395]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M8300_8500.SplitData.node0394 := by
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
  · exact treeEq0395

def B0393 : Block := .branch 165 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B0394, (.leaf 0 [] 0)]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M8300_8500.SplitData.node0393 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0394
  · rfl

def B0392 : Block := .branch 167 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B0393, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M8300_8500.SplitData.node0392 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0393
  · rfl

def B0290 : Block := .branch 98 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0043_0291, B0392, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M8300_8500.SplitData.node0290 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0392
  · rfl
  · rfl

def B0399 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M8300_8500.SplitData.node0399 := by
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

def B0398 : Block := .branch 169 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0399, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M8300_8500.SplitData.node0398 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0399
  · rfl

def B0397 : Block := .branch 170 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158533696280984011454269120520, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), B0398]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M8300_8500.SplitData.node0397 := by
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
  · exact treeEq0398

def B0289 : Block := .branch 86 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0290, B0397, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M8300_8500.SplitData.node0289 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0290
  · exact treeEq0397
  · rfl
  · rfl
  · rfl

def B0288 : Block := .branch 171 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 667).pointIds 667), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 563).pointIds 563), B0289]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M8300_8500.SplitData.node0288 := by
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
  · exact treeEq0289

def B0287 : Block := .branch 168 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 666).pointIds 666), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 561).pointIds 561), B0288]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M8300_8500.SplitData.node0287 := by
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
  · exact treeEq0288

def B0043 : Block := .branch 112 ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![Tip0043_0044, (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), B0287]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M8300_8500.SplitData.node0043 := by
  change Tree.branch (112 : Fin 177) _ = Tree.branch (112 : Fin 177) _
  apply congrArg (Tree.branch (112 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0287

theorem accepted0043 : B0043.accepted = true := by decide +kernel
theorem checked0043 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0043 (maskNeeds ![1267650902460263017706113991041, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576]) := by
  rw [← treeEq0043]
  exact B0043.sound accepted0043
#print axioms checked0043

def B0526 : Block := .branch 161 ![385, 1538, 53268293926769598010497028, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M8300_8500.SplitData.node0526 := by
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
  · rfl

def B0525 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0526, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M8300_8500.SplitData.node0525 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0526
  · rfl
  · rfl
  · rfl

def B0524 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 42535295865117307932921825928971419680, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 540).pointIds 540), B0525]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M8300_8500.SplitData.node0524 := by
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
  · exact treeEq0525

def B0530 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0530 : B0530.tree = HexagonCover.NBand.M8300_8500.SplitData.node0530 := by
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
  · rfl

def B0529 : Block := .branch 135 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0530, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M8300_8500.SplitData.node0529 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530
  · rfl

def B0528 : Block := .branch 161 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626845252854729617484438792706392152104968, 649037107316853453566312041250832, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B0529]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M8300_8500.SplitData.node0528 := by
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
  · exact treeEq0529

def B0527 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0528, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M8300_8500.SplitData.node0527 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl
  · rfl
  · rfl

def B0523 : Block := .branch 125 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0524, B0527]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M8300_8500.SplitData.node0523 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0524
  · exact treeEq0527

def B0534 : Block := .branch 161 ![385, 1538, 53268293926769598010497028, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0534 : B0534.tree = HexagonCover.NBand.M8300_8500.SplitData.node0534 := by
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
  · rfl

def B0533 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0534, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0533 : B0533.tree = HexagonCover.NBand.M8300_8500.SplitData.node0533 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0534
  · rfl
  · rfl
  · rfl

def B0532 : Block := .branch 135 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0533]
theorem treeEq0532 : B0532.tree = HexagonCover.NBand.M8300_8500.SplitData.node0532 := by
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
  · exact treeEq0533

def B0531 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0532, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0531 : B0531.tree = HexagonCover.NBand.M8300_8500.SplitData.node0531 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0532
  · rfl

def B0522 : Block := .branch 121 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0523, (.leaf 5 (Common.fact 256).pointIds 256), B0531]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M8300_8500.SplitData.node0522 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0523
  · rfl
  · exact treeEq0531

def B0539 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0539 : B0539.tree = HexagonCover.NBand.M8300_8500.SplitData.node0539 := by
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

def B0538 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0539, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0538 : B0538.tree = HexagonCover.NBand.M8300_8500.SplitData.node0538 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0539
  · rfl

def B0537 : Block := .branch 163 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0538]
theorem treeEq0537 : B0537.tree = HexagonCover.NBand.M8300_8500.SplitData.node0537 := by
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
  · exact treeEq0538

def B0536 : Block := .branch 165 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0537, (.leaf 0 [] 0)]
theorem treeEq0536 : B0536.tree = HexagonCover.NBand.M8300_8500.SplitData.node0536 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0537
  · rfl

def B0535 : Block := .branch 167 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0536, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0535 : B0535.tree = HexagonCover.NBand.M8300_8500.SplitData.node0535 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0536
  · rfl

def B0521 : Block := .branch 119 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0522, B0535, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M8300_8500.SplitData.node0521 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0522
  · exact treeEq0535
  · rfl
  · rfl

theorem accepted0521 : B0521.accepted = true := by decide +kernel
theorem checked0521 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0521 (maskNeeds ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976]) := by
  rw [← treeEq0521]
  exact B0521.sound accepted0521
#print axioms checked0521

def Tip0520_0521 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0521 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976] checked0521
def B0545 : Block := .branch 161 ![385, 1538, 53268293926769598010497028, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq0545 : B0545.tree = HexagonCover.NBand.M8300_8500.SplitData.node0545 := by
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
  · rfl

def B0544 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0545, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0544 : B0544.tree = HexagonCover.NBand.M8300_8500.SplitData.node0544 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0545
  · rfl
  · rfl
  · rfl

def B0543 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 618).pointIds 618), B0544]
theorem treeEq0543 : B0543.tree = HexagonCover.NBand.M8300_8500.SplitData.node0543 := by
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
  · exact treeEq0544

def B0549 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M8300_8500.SplitData.node0549 := by
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
  · rfl

def B0548 : Block := .branch 135 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0549, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M8300_8500.SplitData.node0548 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0549
  · rfl

def B0547 : Block := .branch 161 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626845252854729617484438792706392152104968, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B0548]
theorem treeEq0547 : B0547.tree = HexagonCover.NBand.M8300_8500.SplitData.node0547 := by
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
  · exact treeEq0548

def B0546 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0547, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M8300_8500.SplitData.node0546 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0547
  · rfl
  · rfl
  · rfl

def B0542 : Block := .branch 125 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0543, B0546]
theorem treeEq0542 : B0542.tree = HexagonCover.NBand.M8300_8500.SplitData.node0542 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0543
  · exact treeEq0546

def B0553 : Block := .branch 161 ![385, 1538, 53268293926769598010497028, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M8300_8500.SplitData.node0553 := by
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
  · rfl

def B0552 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0553, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M8300_8500.SplitData.node0552 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0553
  · rfl
  · rfl
  · rfl

def B0551 : Block := .branch 135 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B0552]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M8300_8500.SplitData.node0551 := by
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
  · exact treeEq0552

def B0550 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0551, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M8300_8500.SplitData.node0550 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0551
  · rfl

def B0541 : Block := .branch 121 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 664614156348782964980578717228097544, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0542, (.leaf 5 (Common.fact 256).pointIds 256), B0550]
theorem treeEq0541 : B0541.tree = HexagonCover.NBand.M8300_8500.SplitData.node0541 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0542
  · rfl
  · exact treeEq0550

def B0558 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M8300_8500.SplitData.node0558 := by
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

def B0557 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0558, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M8300_8500.SplitData.node0557 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0558
  · rfl

def B0556 : Block := .branch 163 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0557]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M8300_8500.SplitData.node0556 := by
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
  · exact treeEq0557

def B0555 : Block := .branch 165 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0556, (.leaf 0 [] 0)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M8300_8500.SplitData.node0555 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0556
  · rfl

def B0554 : Block := .branch 167 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 665263034999774789905469842181423120, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0555, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M8300_8500.SplitData.node0554 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0555
  · rfl

def B0540 : Block := .branch 119 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 41538374868278621028243970634154016, 3367299783582572261937474045661797649400596738342976] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0541, B0554, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0540 : B0540.tree = HexagonCover.NBand.M8300_8500.SplitData.node0540 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0541
  · exact treeEq0554
  · rfl
  · rfl

def B0520 : Block := .branch 115 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976] ![Tip0520_0521, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B0540, (.leaf 0 [] 0)]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M8300_8500.SplitData.node0520 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0540
  · rfl

theorem accepted0520 : B0520.accepted = true := by decide +kernel
theorem checked0520 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0520 (maskNeeds ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976]) := by
  rw [← treeEq0520]
  exact B0520.sound accepted0520
#print axioms checked0520

end HexagonCover.NBand.M8300_8500.SplitTree.Run0006
