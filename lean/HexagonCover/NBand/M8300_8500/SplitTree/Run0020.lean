import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0019
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0020
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip1451_1454 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1454 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0019.checked1454
def Tip1451_1486 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1486 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0019.checked1486
def B1480 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq1480 : B1480.tree = HexagonCover.NBand.M8300_8500.SplitData.node1480 := by
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

def B1479 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1480, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1479 : B1479.tree = HexagonCover.NBand.M8300_8500.SplitData.node1479 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1480
  · rfl
  · rfl

def B1478 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1479, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq1478 : B1478.tree = HexagonCover.NBand.M8300_8500.SplitData.node1478 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1479
  · rfl
  · rfl
  · rfl
  · rfl

def B1477 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1478, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1477 : B1477.tree = HexagonCover.NBand.M8300_8500.SplitData.node1477 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1478
  · rfl
  · rfl

def B1476 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1477, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1476 : B1476.tree = HexagonCover.NBand.M8300_8500.SplitData.node1476 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1477
  · rfl
  · rfl

def B1475 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1476, (.leaf 0 [] 0)]
theorem treeEq1475 : B1475.tree = HexagonCover.NBand.M8300_8500.SplitData.node1475 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1476
  · rfl

def B1474 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1475, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1474 : B1474.tree = HexagonCover.NBand.M8300_8500.SplitData.node1474 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1475
  · rfl

def B1473 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1474, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1473 : B1473.tree = HexagonCover.NBand.M8300_8500.SplitData.node1473 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1474
  · rfl
  · rfl

def B1472 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1473, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1472 : B1472.tree = HexagonCover.NBand.M8300_8500.SplitData.node1472 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1473
  · rfl
  · rfl
  · rfl

def B1471 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B1472]
theorem treeEq1471 : B1471.tree = HexagonCover.NBand.M8300_8500.SplitData.node1471 := by
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
  · exact treeEq1472

def B1470 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1471, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1470 : B1470.tree = HexagonCover.NBand.M8300_8500.SplitData.node1470 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1471
  · rfl

def B1453 : Block := .branch 121 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip1451_1454, (.leaf 5 (Common.fact 256).pointIds 256), B1470]
theorem treeEq1453 : B1453.tree = HexagonCover.NBand.M8300_8500.SplitData.node1453 := by
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
  · exact treeEq1470

def B1485 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1485 : B1485.tree = HexagonCover.NBand.M8300_8500.SplitData.node1485 := by
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

def B1484 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1485, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1484 : B1484.tree = HexagonCover.NBand.M8300_8500.SplitData.node1484 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1485
  · rfl

def B1483 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1484]
theorem treeEq1483 : B1483.tree = HexagonCover.NBand.M8300_8500.SplitData.node1483 := by
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
  · exact treeEq1484

def B1482 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1483, (.leaf 0 [] 0)]
theorem treeEq1482 : B1482.tree = HexagonCover.NBand.M8300_8500.SplitData.node1482 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1483
  · rfl

def B1481 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1482, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1481 : B1481.tree = HexagonCover.NBand.M8300_8500.SplitData.node1481 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1482
  · rfl

def B1452 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1453, B1481, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1452 : B1452.tree = HexagonCover.NBand.M8300_8500.SplitData.node1452 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1453
  · exact treeEq1481
  · rfl
  · rfl

def B1451 : Block := .branch 115 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B1452, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), Tip1451_1486, (.leaf 0 [] 0)]
theorem treeEq1451 : B1451.tree = HexagonCover.NBand.M8300_8500.SplitData.node1451 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1452
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1451 : B1451.accepted = true := by decide +kernel
theorem checked1451 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1451 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1451]
  exact B1451.sound accepted1451
#print axioms checked1451

def Tip1449_1451 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1451 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1451
def B1531 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq1531 : B1531.tree = HexagonCover.NBand.M8300_8500.SplitData.node1531 := by
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
  · rfl

def B1530 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1531, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1530 : B1530.tree = HexagonCover.NBand.M8300_8500.SplitData.node1530 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1531
  · rfl
  · rfl

def B1529 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1530, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 884).pointIds 884)]
theorem treeEq1529 : B1529.tree = HexagonCover.NBand.M8300_8500.SplitData.node1529 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1530
  · rfl
  · rfl
  · rfl
  · rfl

def B1528 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1529, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1528 : B1528.tree = HexagonCover.NBand.M8300_8500.SplitData.node1528 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1529
  · rfl
  · rfl

def B1527 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1528, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1527 : B1527.tree = HexagonCover.NBand.M8300_8500.SplitData.node1527 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1528
  · rfl
  · rfl

def B1526 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1527, (.leaf 0 [] 0)]
theorem treeEq1526 : B1526.tree = HexagonCover.NBand.M8300_8500.SplitData.node1526 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1527
  · rfl

def B1525 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1526, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1525 : B1525.tree = HexagonCover.NBand.M8300_8500.SplitData.node1525 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1526
  · rfl

def B1524 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1525, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1524 : B1524.tree = HexagonCover.NBand.M8300_8500.SplitData.node1524 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1525
  · rfl
  · rfl

def B1523 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 4835703278458516698849288, 178405961588894022239602599634753204089094160, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1524, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1523 : B1523.tree = HexagonCover.NBand.M8300_8500.SplitData.node1523 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1524
  · rfl
  · rfl
  · rfl

def B1522 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1523]
theorem treeEq1522 : B1522.tree = HexagonCover.NBand.M8300_8500.SplitData.node1522 := by
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
  · exact treeEq1523

def B1521 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1522, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1521 : B1521.tree = HexagonCover.NBand.M8300_8500.SplitData.node1521 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1522
  · rfl

def B1450 : Block := .branch 113 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1449_1451, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B1521]
theorem treeEq1450 : B1450.tree = HexagonCover.NBand.M8300_8500.SplitData.node1450 := by
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
  · exact treeEq1521

def B1536 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1536 : B1536.tree = HexagonCover.NBand.M8300_8500.SplitData.node1536 := by
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

def B1535 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1536, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1535 : B1535.tree = HexagonCover.NBand.M8300_8500.SplitData.node1535 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1536
  · rfl

def B1534 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B1535]
theorem treeEq1534 : B1534.tree = HexagonCover.NBand.M8300_8500.SplitData.node1534 := by
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
  · exact treeEq1535

def B1533 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B1534, (.leaf 0 [] 0)]
theorem treeEq1533 : B1533.tree = HexagonCover.NBand.M8300_8500.SplitData.node1533 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1534
  · rfl

def B1532 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B1533, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1532 : B1532.tree = HexagonCover.NBand.M8300_8500.SplitData.node1532 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1533
  · rfl

def B1449 : Block := .branch 108 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B1450, B1532, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1449 : B1449.tree = HexagonCover.NBand.M8300_8500.SplitData.node1449 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1450
  · exact treeEq1532
  · rfl
  · rfl

theorem accepted1449 : B1449.accepted = true := by decide +kernel
theorem checked1449 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1449 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1449]
  exact B1449.sound accepted1449
#print axioms checked1449

def Tip1447_1449 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1449 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1449
def B1547 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq1547 : B1547.tree = HexagonCover.NBand.M8300_8500.SplitData.node1547 := by
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
  · rfl

def B1546 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1547, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1546 : B1546.tree = HexagonCover.NBand.M8300_8500.SplitData.node1546 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1547
  · rfl
  · rfl

def B1545 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1546, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq1545 : B1545.tree = HexagonCover.NBand.M8300_8500.SplitData.node1545 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1546
  · rfl
  · rfl
  · rfl
  · rfl

def B1544 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1545, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1544 : B1544.tree = HexagonCover.NBand.M8300_8500.SplitData.node1544 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1545
  · rfl
  · rfl

def B1543 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1544, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1543 : B1543.tree = HexagonCover.NBand.M8300_8500.SplitData.node1543 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1544
  · rfl
  · rfl

def B1542 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1543, (.leaf 0 [] 0)]
theorem treeEq1542 : B1542.tree = HexagonCover.NBand.M8300_8500.SplitData.node1542 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1543
  · rfl

def B1541 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1542, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1541 : B1541.tree = HexagonCover.NBand.M8300_8500.SplitData.node1541 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1542
  · rfl

def B1540 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1541, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1540 : B1540.tree = HexagonCover.NBand.M8300_8500.SplitData.node1540 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1541
  · rfl
  · rfl

def B1539 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 4835703278458516698849288, 178405961588894022239602599634753204089094160, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1540, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1539 : B1539.tree = HexagonCover.NBand.M8300_8500.SplitData.node1539 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1540
  · rfl
  · rfl
  · rfl

def B1538 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1539]
theorem treeEq1538 : B1538.tree = HexagonCover.NBand.M8300_8500.SplitData.node1538 := by
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
  · exact treeEq1539

def B1537 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1538, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1537 : B1537.tree = HexagonCover.NBand.M8300_8500.SplitData.node1537 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1538
  · rfl

def B1448 : Block := .branch 100 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1447_1449, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B1537]
theorem treeEq1448 : B1448.tree = HexagonCover.NBand.M8300_8500.SplitData.node1448 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1537

def B1552 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1552 : B1552.tree = HexagonCover.NBand.M8300_8500.SplitData.node1552 := by
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

def B1551 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1552, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1551 : B1551.tree = HexagonCover.NBand.M8300_8500.SplitData.node1551 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1552
  · rfl

def B1550 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B1551]
theorem treeEq1550 : B1550.tree = HexagonCover.NBand.M8300_8500.SplitData.node1550 := by
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
  · exact treeEq1551

def B1549 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B1550, (.leaf 0 [] 0)]
theorem treeEq1549 : B1549.tree = HexagonCover.NBand.M8300_8500.SplitData.node1549 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1550
  · rfl

def B1548 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B1549, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1548 : B1548.tree = HexagonCover.NBand.M8300_8500.SplitData.node1548 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1549
  · rfl

def B1447 : Block := .branch 98 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B1448, B1548, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1447 : B1447.tree = HexagonCover.NBand.M8300_8500.SplitData.node1447 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1448
  · exact treeEq1548
  · rfl
  · rfl

theorem accepted1447 : B1447.accepted = true := by decide +kernel
theorem checked1447 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1447 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1447]
  exact B1447.sound accepted1447
#print axioms checked1447

def Tip1444_1447 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1447 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1447
def B1561 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 891).pointIds 891)]
theorem treeEq1561 : B1561.tree = HexagonCover.NBand.M8300_8500.SplitData.node1561 := by
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

def B1560 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1561, (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq1560 : B1560.tree = HexagonCover.NBand.M8300_8500.SplitData.node1560 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1561
  · rfl

def B1559 : Block := .branch 87 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1560, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq1559 : B1559.tree = HexagonCover.NBand.M8300_8500.SplitData.node1559 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1560
  · rfl
  · rfl
  · rfl
  · rfl

def B1558 : Block := .branch 129 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1559, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1558 : B1558.tree = HexagonCover.NBand.M8300_8500.SplitData.node1558 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1559
  · rfl
  · rfl

def B1557 : Block := .branch 138 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1558, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1557 : B1557.tree = HexagonCover.NBand.M8300_8500.SplitData.node1557 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1558
  · rfl
  · rfl

def B1556 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1557, (.leaf 0 [] 0)]
theorem treeEq1556 : B1556.tree = HexagonCover.NBand.M8300_8500.SplitData.node1556 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1557
  · rfl

def B1555 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1556, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1555 : B1555.tree = HexagonCover.NBand.M8300_8500.SplitData.node1555 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1556
  · rfl

def B1554 : Block := .branch 146 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1555, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1554 : B1554.tree = HexagonCover.NBand.M8300_8500.SplitData.node1554 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1555
  · rfl
  · rfl

def B1553 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1554, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq1553 : B1553.tree = HexagonCover.NBand.M8300_8500.SplitData.node1553 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1554
  · rfl
  · rfl
  · rfl

def B1446 : Block := .branch 90 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1444_1447, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B1553]
theorem treeEq1446 : B1446.tree = HexagonCover.NBand.M8300_8500.SplitData.node1446 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1553

def B1564 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1564 : B1564.tree = HexagonCover.NBand.M8300_8500.SplitData.node1564 := by
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

def B1563 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1564, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1563 : B1563.tree = HexagonCover.NBand.M8300_8500.SplitData.node1563 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1564
  · rfl

def B1562 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79310369469998132377423994888, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1563]
theorem treeEq1562 : B1562.tree = HexagonCover.NBand.M8300_8500.SplitData.node1562 := by
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
  · exact treeEq1563

def B1445 : Block := .branch 86 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B1446, B1562, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1445 : B1445.tree = HexagonCover.NBand.M8300_8500.SplitData.node1445 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1446
  · exact treeEq1562
  · rfl
  · rfl
  · rfl

def B1567 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1567 : B1567.tree = HexagonCover.NBand.M8300_8500.SplitData.node1567 := by
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

def B1566 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1567, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1566 : B1566.tree = HexagonCover.NBand.M8300_8500.SplitData.node1566 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1567
  · rfl

def B1565 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237728008872299139430921297928, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 893).pointIds 893), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1566]
theorem treeEq1565 : B1565.tree = HexagonCover.NBand.M8300_8500.SplitData.node1565 := by
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
  · exact treeEq1566

def B1444 : Block := .branch 85 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B1445, B1565, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq1444 : B1444.tree = HexagonCover.NBand.M8300_8500.SplitData.node1444 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1445
  · exact treeEq1565
  · rfl
  · rfl
  · rfl

theorem accepted1444 : B1444.accepted = true := by decide +kernel
theorem checked1444 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1444 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1444]
  exact B1444.sound accepted1444
#print axioms checked1444

end HexagonCover.NBand.M8300_8500.SplitTree.Run0020
