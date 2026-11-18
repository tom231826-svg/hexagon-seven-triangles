import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0016
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0017
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip1283_1285 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1285 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0016.checked1285
def B1312 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq1312 : B1312.tree = HexagonCover.NBand.M8300_8500.SplitData.node1312 := by
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

def B1311 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1312, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1311 : B1311.tree = HexagonCover.NBand.M8300_8500.SplitData.node1311 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1312
  · rfl
  · rfl

def B1310 : Block := .branch 166 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B1311, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1310 : B1310.tree = HexagonCover.NBand.M8300_8500.SplitData.node1310 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1311
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1309 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1310, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq1309 : B1309.tree = HexagonCover.NBand.M8300_8500.SplitData.node1309 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1310
  · rfl
  · rfl
  · rfl
  · rfl

def B1308 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1309, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1308 : B1308.tree = HexagonCover.NBand.M8300_8500.SplitData.node1308 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1309
  · rfl
  · rfl

def B1307 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1308, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1307 : B1307.tree = HexagonCover.NBand.M8300_8500.SplitData.node1307 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1308
  · rfl
  · rfl

def B1306 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1307, (.leaf 0 [] 0)]
theorem treeEq1306 : B1306.tree = HexagonCover.NBand.M8300_8500.SplitData.node1306 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1307
  · rfl

def B1305 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1306, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1305 : B1305.tree = HexagonCover.NBand.M8300_8500.SplitData.node1305 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1306
  · rfl

def B1304 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1305, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1304 : B1304.tree = HexagonCover.NBand.M8300_8500.SplitData.node1304 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1305
  · rfl
  · rfl

def B1303 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422335658661502629357934307808096157728, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1304, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1303 : B1303.tree = HexagonCover.NBand.M8300_8500.SplitData.node1303 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1304
  · rfl
  · rfl
  · rfl

def B1302 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422335658661502629357934307808096157728, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B1303]
theorem treeEq1302 : B1302.tree = HexagonCover.NBand.M8300_8500.SplitData.node1302 := by
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
  · exact treeEq1303

def B1301 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1302, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1301 : B1301.tree = HexagonCover.NBand.M8300_8500.SplitData.node1301 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1302
  · rfl

def B1284 : Block := .branch 121 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip1283_1285, (.leaf 5 (Common.fact 256).pointIds 256), B1301]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M8300_8500.SplitData.node1284 := by
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
  · exact treeEq1301

def B1317 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1317 : B1317.tree = HexagonCover.NBand.M8300_8500.SplitData.node1317 := by
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

def B1316 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1317, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1316 : B1316.tree = HexagonCover.NBand.M8300_8500.SplitData.node1316 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1317
  · rfl

def B1315 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1316]
theorem treeEq1315 : B1315.tree = HexagonCover.NBand.M8300_8500.SplitData.node1315 := by
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
  · exact treeEq1316

def B1314 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1315, (.leaf 0 [] 0)]
theorem treeEq1314 : B1314.tree = HexagonCover.NBand.M8300_8500.SplitData.node1314 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1315
  · rfl

def B1313 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1314, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1313 : B1313.tree = HexagonCover.NBand.M8300_8500.SplitData.node1313 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1314
  · rfl

def B1283 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1284, B1313, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M8300_8500.SplitData.node1283 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1284
  · exact treeEq1313
  · rfl
  · rfl

theorem accepted1283 : B1283.accepted = true := by decide +kernel
theorem checked1283 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1283 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1283]
  exact B1283.sound accepted1283
#print axioms checked1283

def Tip1248_1251 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1251 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0016.checked1251
def Tip1248_1283 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1283 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] checked1283
def B1277 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M8300_8500.SplitData.node1277 := by
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

def B1276 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1277, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M8300_8500.SplitData.node1276 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1277
  · rfl
  · rfl

def B1275 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1276, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M8300_8500.SplitData.node1275 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1276
  · rfl
  · rfl
  · rfl
  · rfl

def B1274 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1275, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M8300_8500.SplitData.node1274 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1275
  · rfl
  · rfl

def B1273 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1274, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M8300_8500.SplitData.node1273 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl
  · rfl

def B1272 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1273, (.leaf 0 [] 0)]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M8300_8500.SplitData.node1272 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1273
  · rfl

def B1271 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1272, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M8300_8500.SplitData.node1271 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1272
  · rfl

def B1270 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1271, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M8300_8500.SplitData.node1270 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1271
  · rfl
  · rfl

def B1269 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 393248, 3367299783626136380271328878480347021994224751476800] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1270, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M8300_8500.SplitData.node1269 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1270
  · rfl
  · rfl
  · rfl

def B1268 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405961588894022239602599634753204089094160, 748288838313422294120286634350736906063837462396960, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B1269]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M8300_8500.SplitData.node1268 := by
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
  · exact treeEq1269

def B1267 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582580237305448755157035072242958420410432] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1268, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M8300_8500.SplitData.node1267 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1268
  · rfl

def B1250 : Block := .branch 121 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip1248_1251, (.leaf 5 (Common.fact 256).pointIds 256), B1267]
theorem treeEq1250 : B1250.tree = HexagonCover.NBand.M8300_8500.SplitData.node1250 := by
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
  · exact treeEq1267

def B1282 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M8300_8500.SplitData.node1282 := by
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

def B1281 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1282, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M8300_8500.SplitData.node1281 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1282
  · rfl

def B1280 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1281]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M8300_8500.SplitData.node1280 := by
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
  · exact treeEq1281

def B1279 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1280, (.leaf 0 [] 0)]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M8300_8500.SplitData.node1279 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1280
  · rfl

def B1278 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1279, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M8300_8500.SplitData.node1278 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1279
  · rfl

def B1249 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1250, B1278, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1249 : B1249.tree = HexagonCover.NBand.M8300_8500.SplitData.node1249 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1250
  · exact treeEq1278
  · rfl
  · rfl

def B1248 : Block := .branch 115 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B1249, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), Tip1248_1283, (.leaf 0 [] 0)]
theorem treeEq1248 : B1248.tree = HexagonCover.NBand.M8300_8500.SplitData.node1248 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1248 : B1248.accepted = true := by decide +kernel
theorem checked1248 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1248 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1248]
  exact B1248.sound accepted1248
#print axioms checked1248

def Tip1246_1248 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1248 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1248
def B1328 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq1328 : B1328.tree = HexagonCover.NBand.M8300_8500.SplitData.node1328 := by
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

def B1327 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1328, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1327 : B1327.tree = HexagonCover.NBand.M8300_8500.SplitData.node1327 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1328
  · rfl
  · rfl

def B1326 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1327, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 884).pointIds 884)]
theorem treeEq1326 : B1326.tree = HexagonCover.NBand.M8300_8500.SplitData.node1326 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1327
  · rfl
  · rfl
  · rfl
  · rfl

def B1325 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1326, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1325 : B1325.tree = HexagonCover.NBand.M8300_8500.SplitData.node1325 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1326
  · rfl
  · rfl

def B1324 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1325, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1324 : B1324.tree = HexagonCover.NBand.M8300_8500.SplitData.node1324 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1325
  · rfl
  · rfl

def B1323 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1324, (.leaf 0 [] 0)]
theorem treeEq1323 : B1323.tree = HexagonCover.NBand.M8300_8500.SplitData.node1323 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1324
  · rfl

def B1322 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1323, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1322 : B1322.tree = HexagonCover.NBand.M8300_8500.SplitData.node1322 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1323
  · rfl

def B1321 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1322, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1321 : B1321.tree = HexagonCover.NBand.M8300_8500.SplitData.node1321 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1322
  · rfl
  · rfl

def B1320 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 4835703278458516698849288, 178405961588894022239602599634753204089094160, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1321, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1320 : B1320.tree = HexagonCover.NBand.M8300_8500.SplitData.node1320 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1321
  · rfl
  · rfl
  · rfl

def B1319 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1320]
theorem treeEq1319 : B1319.tree = HexagonCover.NBand.M8300_8500.SplitData.node1319 := by
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
  · exact treeEq1320

def B1318 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1319, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1318 : B1318.tree = HexagonCover.NBand.M8300_8500.SplitData.node1318 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1319
  · rfl

def B1247 : Block := .branch 113 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1246_1248, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B1318]
theorem treeEq1247 : B1247.tree = HexagonCover.NBand.M8300_8500.SplitData.node1247 := by
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
  · exact treeEq1318

def B1333 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1333 : B1333.tree = HexagonCover.NBand.M8300_8500.SplitData.node1333 := by
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

def B1332 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1333, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1332 : B1332.tree = HexagonCover.NBand.M8300_8500.SplitData.node1332 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1333
  · rfl

def B1331 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B1332]
theorem treeEq1331 : B1331.tree = HexagonCover.NBand.M8300_8500.SplitData.node1331 := by
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
  · exact treeEq1332

def B1330 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B1331, (.leaf 0 [] 0)]
theorem treeEq1330 : B1330.tree = HexagonCover.NBand.M8300_8500.SplitData.node1330 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1331
  · rfl

def B1329 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B1330, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1329 : B1329.tree = HexagonCover.NBand.M8300_8500.SplitData.node1329 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1330
  · rfl

def B1246 : Block := .branch 108 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B1247, B1329, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1246 : B1246.tree = HexagonCover.NBand.M8300_8500.SplitData.node1246 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1247
  · exact treeEq1329
  · rfl
  · rfl

theorem accepted1246 : B1246.accepted = true := by decide +kernel
theorem checked1246 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1246 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1246]
  exact B1246.sound accepted1246
#print axioms checked1246

def Tip1244_1246 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1246 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1246
def B1344 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq1344 : B1344.tree = HexagonCover.NBand.M8300_8500.SplitData.node1344 := by
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

def B1343 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B1344, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1343 : B1343.tree = HexagonCover.NBand.M8300_8500.SplitData.node1343 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1344
  · rfl
  · rfl

def B1342 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B1343, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq1342 : B1342.tree = HexagonCover.NBand.M8300_8500.SplitData.node1342 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1343
  · rfl
  · rfl
  · rfl
  · rfl

def B1341 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1342, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1341 : B1341.tree = HexagonCover.NBand.M8300_8500.SplitData.node1341 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1342
  · rfl
  · rfl

def B1340 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1341, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1340 : B1340.tree = HexagonCover.NBand.M8300_8500.SplitData.node1340 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1341
  · rfl
  · rfl

def B1339 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1340, (.leaf 0 [] 0)]
theorem treeEq1339 : B1339.tree = HexagonCover.NBand.M8300_8500.SplitData.node1339 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1340
  · rfl

def B1338 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1339, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1338 : B1338.tree = HexagonCover.NBand.M8300_8500.SplitData.node1338 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1339
  · rfl

def B1337 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1338, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1337 : B1337.tree = HexagonCover.NBand.M8300_8500.SplitData.node1337 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1338
  · rfl
  · rfl

def B1336 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 4835703278458516698849288, 178405961588894022239602599634753204089094160, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1337, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1336 : B1336.tree = HexagonCover.NBand.M8300_8500.SplitData.node1336 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1337
  · rfl
  · rfl
  · rfl

def B1335 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1336]
theorem treeEq1335 : B1335.tree = HexagonCover.NBand.M8300_8500.SplitData.node1335 := by
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
  · exact treeEq1336

def B1334 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1335, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1334 : B1334.tree = HexagonCover.NBand.M8300_8500.SplitData.node1334 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1335
  · rfl

def B1245 : Block := .branch 100 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1244_1246, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B1334]
theorem treeEq1245 : B1245.tree = HexagonCover.NBand.M8300_8500.SplitData.node1245 := by
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
  · exact treeEq1334

def B1349 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1349 : B1349.tree = HexagonCover.NBand.M8300_8500.SplitData.node1349 := by
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

def B1348 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1349, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1348 : B1348.tree = HexagonCover.NBand.M8300_8500.SplitData.node1348 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1349
  · rfl

def B1347 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B1348]
theorem treeEq1347 : B1347.tree = HexagonCover.NBand.M8300_8500.SplitData.node1347 := by
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
  · exact treeEq1348

def B1346 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B1347, (.leaf 0 [] 0)]
theorem treeEq1346 : B1346.tree = HexagonCover.NBand.M8300_8500.SplitData.node1346 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1347
  · rfl

def B1345 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B1346, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1345 : B1345.tree = HexagonCover.NBand.M8300_8500.SplitData.node1345 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1346
  · rfl

def B1244 : Block := .branch 98 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B1245, B1345, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1244 : B1244.tree = HexagonCover.NBand.M8300_8500.SplitData.node1244 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1245
  · exact treeEq1345
  · rfl
  · rfl

theorem accepted1244 : B1244.accepted = true := by decide +kernel
theorem checked1244 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1244 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1244]
  exact B1244.sound accepted1244
#print axioms checked1244

end HexagonCover.NBand.M8300_8500.SplitTree.Run0017
