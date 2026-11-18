import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0014
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0015
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1205 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1205 : B1205.tree = HexagonCover.NBand.M6900_7100.SplitData.node1205 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1204 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B1205, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq1204 : B1204.tree = HexagonCover.NBand.M6900_7100.SplitData.node1204 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1205
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1203 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B1204, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1203 : B1203.tree = HexagonCover.NBand.M6900_7100.SplitData.node1203 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1204
  · rfl
  · rfl
  · rfl
  · rfl

def B1202 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1203, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1202 : B1202.tree = HexagonCover.NBand.M6900_7100.SplitData.node1202 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1203
  · rfl
  · rfl
  · rfl
  · rfl

def B1201 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1202, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1201 : B1201.tree = HexagonCover.NBand.M6900_7100.SplitData.node1201 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1202
  · rfl
  · rfl
  · rfl

def B1200 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1201, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq1200 : B1200.tree = HexagonCover.NBand.M6900_7100.SplitData.node1200 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1201
  · rfl
  · rfl

def B1199 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1200]
theorem treeEq1199 : B1199.tree = HexagonCover.NBand.M6900_7100.SplitData.node1199 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1200

def B1198 : Block := .branch 166 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B1199, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1198 : B1198.tree = HexagonCover.NBand.M6900_7100.SplitData.node1198 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1199
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1197 : Block := .branch 151 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1198, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1197 : B1197.tree = HexagonCover.NBand.M6900_7100.SplitData.node1197 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1198
  · rfl

def B1209 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1209 : B1209.tree = HexagonCover.NBand.M6900_7100.SplitData.node1209 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1208 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1209, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1208 : B1208.tree = HexagonCover.NBand.M6900_7100.SplitData.node1208 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1209
  · rfl
  · rfl

def B1207 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1208]
theorem treeEq1207 : B1207.tree = HexagonCover.NBand.M6900_7100.SplitData.node1207 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1208

def B1213 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq1213 : B1213.tree = HexagonCover.NBand.M6900_7100.SplitData.node1213 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1212 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1213, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq1212 : B1212.tree = HexagonCover.NBand.M6900_7100.SplitData.node1212 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1213
  · rfl
  · rfl

def B1211 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1212]
theorem treeEq1211 : B1211.tree = HexagonCover.NBand.M6900_7100.SplitData.node1211 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1212

def B1215 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1215 : B1215.tree = HexagonCover.NBand.M6900_7100.SplitData.node1215 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1214 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1215, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1214 : B1214.tree = HexagonCover.NBand.M6900_7100.SplitData.node1214 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1215
  · rfl
  · rfl

def B1210 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1211, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1214]
theorem treeEq1210 : B1210.tree = HexagonCover.NBand.M6900_7100.SplitData.node1210 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1211
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1214

def B1206 : Block := .branch 90 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1207, B1210, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1206 : B1206.tree = HexagonCover.NBand.M6900_7100.SplitData.node1206 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1207
  · exact treeEq1210
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1196 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1197, (.leaf 5 (Common.fact 163).pointIds 163), B1206]
theorem treeEq1196 : B1196.tree = HexagonCover.NBand.M6900_7100.SplitData.node1196 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1197
  · rfl
  · exact treeEq1206

theorem accepted1196 : B1196.accepted = true := by decide +kernel
theorem checked1196 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1196 (maskNeeds ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq1196]
  exact B1196.sound accepted1196
#print axioms checked1196

def Tip1160_1169 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1169 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] HexagonCover.NBand.M6900_7100.SplitTree.Run0014.checked1169
def Tip1160_1196 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1196 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked1196
def B1167 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M6900_7100.SplitData.node1167 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1166 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1167, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M6900_7100.SplitData.node1166 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1167
  · rfl
  · rfl

def B1165 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1166]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M6900_7100.SplitData.node1165 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1166

def B1190 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq1190 : B1190.tree = HexagonCover.NBand.M6900_7100.SplitData.node1190 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1189 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1190, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq1189 : B1189.tree = HexagonCover.NBand.M6900_7100.SplitData.node1189 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1190
  · rfl
  · rfl

def B1168 : Block := .branch 112 ![748288838313422304504880351420982458935188826096001, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip1160_1169, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1189]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M6900_7100.SplitData.node1168 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1189

def B1164 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 618970462436606600028358146, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B1165, B1168, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M6900_7100.SplitData.node1164 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1165
  · exact treeEq1168
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1194 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1194 : B1194.tree = HexagonCover.NBand.M6900_7100.SplitData.node1194 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1193 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1194, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq1193 : B1193.tree = HexagonCover.NBand.M6900_7100.SplitData.node1193 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1194
  · rfl
  · rfl

def B1192 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1193]
theorem treeEq1192 : B1192.tree = HexagonCover.NBand.M6900_7100.SplitData.node1192 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1193

def B1217 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M6900_7100.SplitData.node1217 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1216 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1217, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M6900_7100.SplitData.node1216 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1217
  · rfl
  · rfl

def B1195 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip1160_1196, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B1216]
theorem treeEq1195 : B1195.tree = HexagonCover.NBand.M6900_7100.SplitData.node1195 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1216

def B1191 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 618971052732416958734009858, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B1192, B1195, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq1191 : B1191.tree = HexagonCover.NBand.M6900_7100.SplitData.node1191 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1192
  · exact treeEq1195
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1163 : Block := .branch 69 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B1164, B1191, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M6900_7100.SplitData.node1163 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1164
  · exact treeEq1191
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1162 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 2398076729582241716228, 38690348594151003235835912, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1163, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M6900_7100.SplitData.node1162 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1163
  · rfl
  · rfl

def B1161 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1162, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M6900_7100.SplitData.node1161 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1162
  · rfl

def B1160 : Block := .branch 169 ![10387129018270111715863986064851329, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B1161, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M6900_7100.SplitData.node1160 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1161
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1160 : B1160.accepted = true := by decide +kernel
theorem checked1160 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1160 (maskNeeds ![10387129018270111715863986064851329, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq1160]
  exact B1160.sound accepted1160
#print axioms checked1160

def Tip1145_1160 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1160 ![10387129018270111715863986064851329, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] checked1160
def B1159 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 487).pointIds 487), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M6900_7100.SplitData.node1159 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1158 : Block := .branch 159 ![748288838313443561768219193004703366976801947517313, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 484).pointIds 484), B1159, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 485).pointIds 485)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M6900_7100.SplitData.node1158 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1159
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1157 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![B1158, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 483).pointIds 483)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M6900_7100.SplitData.node1157 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1158
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1156 : Block := .branch 161 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38690348594151003235835912, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1157, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq1156 : B1156.tree = HexagonCover.NBand.M6900_7100.SplitData.node1156 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1157
  · rfl
  · rfl
  · rfl
  · rfl

def B1155 : Block := .branch 137 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1156, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1155 : B1155.tree = HexagonCover.NBand.M6900_7100.SplitData.node1155 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1156
  · rfl
  · rfl
  · rfl

def B1154 : Block := .branch 162 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1155, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq1154 : B1154.tree = HexagonCover.NBand.M6900_7100.SplitData.node1154 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1155
  · rfl
  · rfl

def B1153 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38690348594151003235835912, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B1154]
theorem treeEq1153 : B1153.tree = HexagonCover.NBand.M6900_7100.SplitData.node1153 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1154

def B1152 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38690348594151003235835912, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1153, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1152 : B1152.tree = HexagonCover.NBand.M6900_7100.SplitData.node1152 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1153
  · rfl
  · rfl

def B1151 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 1099511629314, 6148, 38690348594151003235835912, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1152, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1151 : B1151.tree = HexagonCover.NBand.M6900_7100.SplitData.node1151 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1152
  · rfl

def B1150 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![B1151, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq1150 : B1150.tree = HexagonCover.NBand.M6900_7100.SplitData.node1150 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1151
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1149 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B1150]
theorem treeEq1149 : B1149.tree = HexagonCover.NBand.M6900_7100.SplitData.node1149 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1150

def B1148 : Block := .branch 166 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B1149, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1148 : B1148.tree = HexagonCover.NBand.M6900_7100.SplitData.node1148 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1147 : Block := .branch 151 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B1148, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1147 : B1147.tree = HexagonCover.NBand.M6900_7100.SplitData.node1147 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1148
  · rfl

def B1146 : Block := .branch 108 ![10387129018270111715863986064851329, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B1147, (.leaf 5 (Common.fact 322).pointIds 322), Tip1145_1160]
theorem treeEq1146 : B1146.tree = HexagonCover.NBand.M6900_7100.SplitData.node1146 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1147
  · rfl
  · rfl

def B1222 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq1222 : B1222.tree = HexagonCover.NBand.M6900_7100.SplitData.node1222 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1221 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1222, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M6900_7100.SplitData.node1221 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1222
  · rfl
  · rfl

def B1220 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B1221, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M6900_7100.SplitData.node1220 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1221
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1219 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1220, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M6900_7100.SplitData.node1219 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1220
  · rfl

def B1218 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1219, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M6900_7100.SplitData.node1218 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1219
  · rfl
  · rfl

def B1145 : Block := .branch 101 ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B1146, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B1218]
theorem treeEq1145 : B1145.tree = HexagonCover.NBand.M6900_7100.SplitData.node1145 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1146
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1218

theorem accepted1145 : B1145.accepted = true := by decide +kernel
theorem checked1145 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1145 (maskNeeds ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1145]
  exact B1145.sound accepted1145
#print axioms checked1145

def Tip1143_1145 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1145 ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked1145
def B1227 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M6900_7100.SplitData.node1227 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1226 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1227, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1226 : B1226.tree = HexagonCover.NBand.M6900_7100.SplitData.node1226 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1227
  · rfl
  · rfl

def B1225 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218543403231594674788036628713046080] ![B1226, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M6900_7100.SplitData.node1225 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1224 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1225, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1224 : B1224.tree = HexagonCover.NBand.M6900_7100.SplitData.node1224 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1225
  · rfl

def B1223 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1224, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1223 : B1223.tree = HexagonCover.NBand.M6900_7100.SplitData.node1223 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1224
  · rfl
  · rfl

def B1144 : Block := .branch 91 ![10384593717069655257060992658440577, 618970463301297728483493378, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip1143_1145, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B1223]
theorem treeEq1144 : B1144.tree = HexagonCover.NBand.M6900_7100.SplitData.node1144 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1223

def B1237 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M6900_7100.SplitData.node1237 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1236 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1237, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M6900_7100.SplitData.node1236 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1237
  · rfl

def B1235 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![B1236, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M6900_7100.SplitData.node1235 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1236
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1234 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B1235]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M6900_7100.SplitData.node1234 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1235

def B1233 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B1234, (.leaf 0 [] 0)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M6900_7100.SplitData.node1233 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1234
  · rfl

def B1232 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B1233, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M6900_7100.SplitData.node1232 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1233
  · rfl

def B1231 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B1232, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M6900_7100.SplitData.node1231 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1232
  · rfl
  · rfl

def B1230 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![B1231, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M6900_7100.SplitData.node1230 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1231
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1229 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1230, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M6900_7100.SplitData.node1229 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1230
  · rfl

def B1228 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1229, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M6900_7100.SplitData.node1228 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1229
  · rfl
  · rfl

def B1143 : Block := .branch 89 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B1144, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1228]
theorem treeEq1143 : B1143.tree = HexagonCover.NBand.M6900_7100.SplitData.node1143 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1144
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1228

theorem accepted1143 : B1143.accepted = true := by decide +kernel
theorem checked1143 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1143 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1143]
  exact B1143.sound accepted1143
#print axioms checked1143

end HexagonCover.NBand.M6900_7100.SplitTree.Run0015
