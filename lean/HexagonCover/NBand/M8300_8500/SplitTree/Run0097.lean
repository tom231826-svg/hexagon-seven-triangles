import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0096
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0097
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6362_6364 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6364 ![385, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] HexagonCover.NBand.M8300_8500.SplitTree.Run0096.checked6364
def B7014 : Block := .branch 143 ![385, 1538, 6148, 24584, 2857282978561736090009263903683071317953839120, 393248, 65339531360803324799575267307519020105792] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 1388).pointIds 1388), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1389).pointIds 1389)]
theorem treeEq7014 : B7014.tree = HexagonCover.NBand.M8300_8500.SplitData.node7014 := by
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
  · rfl

def B7013 : Block := .branch 135 ![385, 1538, 6148, 24584, 2857282978561736090009263903683071317953839120, 748288838313422294120286634350736906063837462396960, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B7014]
theorem treeEq7013 : B7013.tree = HexagonCover.NBand.M8300_8500.SplitData.node7013 := by
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
  · exact treeEq7014

def B7012 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 2857282978561736090009263903683071317953839120, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1386).pointIds 1386), B7013, (.leaf 6 (Common.fact 1387).pointIds 1387)]
theorem treeEq7012 : B7012.tree = HexagonCover.NBand.M8300_8500.SplitData.node7012 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7013
  · rfl

def B7011 : Block := .branch 141 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), B7012, (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 1385).pointIds 1385)]
theorem treeEq7011 : B7011.tree = HexagonCover.NBand.M8300_8500.SplitData.node7011 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7012
  · rfl
  · rfl

def B7010 : Block := .branch 147 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7011, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1384).pointIds 1384)]
theorem treeEq7010 : B7010.tree = HexagonCover.NBand.M8300_8500.SplitData.node7010 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7011
  · rfl
  · rfl

def B7009 : Block := .branch 148 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7010, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1383).pointIds 1383)]
theorem treeEq7009 : B7009.tree = HexagonCover.NBand.M8300_8500.SplitData.node7009 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7010
  · rfl
  · rfl

def B7008 : Block := .branch 149 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1365).pointIds 1365), (.leaf 1 (Common.fact 1366).pointIds 1366), (.leaf 2 (Common.fact 1367).pointIds 1367), (.leaf 3 (Common.fact 1368).pointIds 1368), B7009, (.leaf 5 (Common.fact 1369).pointIds 1369), (.leaf 6 (Common.fact 1382).pointIds 1382)]
theorem treeEq7008 : B7008.tree = HexagonCover.NBand.M8300_8500.SplitData.node7008 := by
  change Tree.branch (149 : Fin 177) _ = Tree.branch (149 : Fin 177) _
  apply congrArg (Tree.branch (149 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7009
  · rfl
  · rfl

def B7007 : Block := .branch 150 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7008, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1381).pointIds 1381)]
theorem treeEq7007 : B7007.tree = HexagonCover.NBand.M8300_8500.SplitData.node7007 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7008
  · rfl
  · rfl

def B7006 : Block := .branch 128 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B7007, (.leaf 4 (Common.fact 1358).pointIds 1358), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1380).pointIds 1380)]
theorem treeEq7006 : B7006.tree = HexagonCover.NBand.M8300_8500.SplitData.node7006 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7007
  · rfl
  · rfl
  · rfl

def B7005 : Block := .branch 151 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7006, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1379).pointIds 1379)]
theorem treeEq7005 : B7005.tree = HexagonCover.NBand.M8300_8500.SplitData.node7005 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7006
  · rfl
  · rfl

def B7004 : Block := .branch 168 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201476263317556252689039424] ![B7005, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq7004 : B7004.tree = HexagonCover.NBand.M8300_8500.SplitData.node7004 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6363 : Block := .branch 77 ![385, 758927455711921666, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 163).pointIds 163), Tip6362_6364, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7004]
theorem treeEq6363 : B6363.tree = HexagonCover.NBand.M8300_8500.SplitData.node6363 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7004

def B7018 : Block := .branch 143 ![385, 1538, 6148, 24584, 696898287454081973172991196020261297160208, 393248, 2993155353275472564876069738765874146222731051925568] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1393).pointIds 1393)]
theorem treeEq7018 : B7018.tree = HexagonCover.NBand.M8300_8500.SplitData.node7018 := by
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
  · rfl

def B7017 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 2993886104094138016335171581182232287732559018197056] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B7018, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1392).pointIds 1392)]
theorem treeEq7017 : B7017.tree = HexagonCover.NBand.M8300_8500.SplitData.node7017 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7018
  · rfl
  · rfl

def B7016 : Block := .branch 159 ![374144419156711147060143317175958748842277436653953, 146437906389534210, 6148, 81129638414606681695789005168648, 98320, 393248, 2993155353275472564876069738765874146222731051925568] ![(.leaf 0 (Common.fact 1390).pointIds 1390), (.leaf 1 (Common.fact 1391).pointIds 1391), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B7017]
theorem treeEq7016 : B7016.tree = HexagonCover.NBand.M8300_8500.SplitData.node7016 := by
  change Tree.branch (159 : Fin 177) _ = Tree.branch (159 : Fin 177) _
  apply congrArg (Tree.branch (159 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7017

def B7015 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738765874146222731051925568] ![B7016, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq7015 : B7015.tree = HexagonCover.NBand.M8300_8500.SplitData.node7015 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6362 : Block := .branch 75 ![590295810358705652097, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B6363, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7015]
theorem treeEq6362 : B6362.tree = HexagonCover.NBand.M8300_8500.SplitData.node6362 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6363
  · rfl
  · rfl
  · rfl
  · exact treeEq7015

theorem accepted6362 : B6362.accepted = true := by decide +kernel
theorem checked6362 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6362 (maskNeeds ![590295810358705652097, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq6362]
  exact B6362.sound accepted6362
#print axioms checked6362

def B7043 : Block := .branch 138 ![385, 1538, 6148, 18889465931478580879368, 100353353393387804136910732226917626777010192, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 1425).pointIds 1425), (.leaf 4 (Common.fact 1426).pointIds 1426), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1427).pointIds 1427)]
theorem treeEq7043 : B7043.tree = HexagonCover.NBand.M8300_8500.SplitData.node7043 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7042 : Block := .branch 143 ![385, 1538, 6148, 18889465931478580879368, 89202980794122492566142873090593446024019984, 393248, 2993886104105021735327076205466031620145942416064576] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7043, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1424).pointIds 1424)]
theorem treeEq7042 : B7042.tree = HexagonCover.NBand.M8300_8500.SplitData.node7042 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7043
  · rfl
  · rfl

def B7041 : Block := .branch 107 ![385, 1538, 6148, 18889465931478580879368, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 1422).pointIds 1422), (.leaf 4 (Common.fact 1423).pointIds 1423), (.leaf 5 (Common.fact 780).pointIds 780), B7042]
theorem treeEq7041 : B7041.tree = HexagonCover.NBand.M8300_8500.SplitData.node7041 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7042

def B7040 : Block := .branch 165 ![385, 1538, 6148, 18889465931478580879368, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1421).pointIds 1421), B7041, (.leaf 0 [] 0)]
theorem treeEq7040 : B7040.tree = HexagonCover.NBand.M8300_8500.SplitData.node7040 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7041
  · rfl

def B7039 : Block := .branch 167 ![385, 1538, 6148, 18889465931478580879368, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1420).pointIds 1420), B7040, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7039 : B7039.tree = HexagonCover.NBand.M8300_8500.SplitData.node7039 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7040
  · rfl

def B7038 : Block := .branch 151 ![385, 1538, 6148, 18889465931478580879368, 89202980794122492566142873090593446024019984, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7039, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1419).pointIds 1419)]
theorem treeEq7038 : B7038.tree = HexagonCover.NBand.M8300_8500.SplitData.node7038 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7039
  · rfl
  · rfl

def B7037 : Block := .branch 97 ![385, 1538, 6148, 18889465931478580879368, 89202980794122492566142873090593446024019984, 393248, 2993886104105021735164658472311789728079177317875776] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 1418).pointIds 1418), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B7038]
theorem treeEq7037 : B7037.tree = HexagonCover.NBand.M8300_8500.SplitData.node7037 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7038

def B7036 : Block := .branch 133 ![385, 1538, 6148, 18889465931478580879368, 267608942382367477698428619271780338071863312, 393248, 2993886104094132699423188441480961740641360735109184] ![(.leaf 0 (Common.fact 1412).pointIds 1412), (.leaf 1 (Common.fact 1413).pointIds 1413), (.leaf 2 (Common.fact 1414).pointIds 1414), (.leaf 3 (Common.fact 1415).pointIds 1415), (.leaf 4 (Common.fact 1416).pointIds 1416), (.leaf 5 (Common.fact 1417).pointIds 1417), B7037]
theorem treeEq7036 : B7036.tree = HexagonCover.NBand.M8300_8500.SplitData.node7036 := by
  change Tree.branch (133 : Fin 177) _ = Tree.branch (133 : Fin 177) _
  apply congrArg (Tree.branch (133 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7037

def B7035 : Block := .branch 159 ![374144419156711147060143317175958748842277436653953, 146437906389534210, 6148, 18889465931478580879368, 267608942382367477698428619271780338071863312, 393248, 2993155353275467247964086599064603599131532768837696] ![(.leaf 0 (Common.fact 1390).pointIds 1390), (.leaf 1 (Common.fact 1391).pointIds 1391), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B7036]
theorem treeEq7035 : B7035.tree = HexagonCover.NBand.M8300_8500.SplitData.node7035 := by
  change Tree.branch (159 : Fin 177) _ = Tree.branch (159 : Fin 177) _
  apply congrArg (Tree.branch (159 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7036

def B7034 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228181403730269072124829704, 267608942382367477698428619271780338071863312, 393248, 2999001359824796176548884478058960346438397620387904] ![B7035, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1411).pointIds 1411)]
theorem treeEq7034 : B7034.tree = HexagonCover.NBand.M8300_8500.SplitData.node7034 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7035
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7033 : Block := .branch 162 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228181403730269072124829704, 267608942382367477698428619271780338071863312, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1410).pointIds 1410), (.leaf 5 (Common.fact 358).pointIds 358), B7034]
theorem treeEq7033 : B7033.tree = HexagonCover.NBand.M8300_8500.SplitData.node7033 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7034

def B7032 : Block := .branch 146 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228181403730269072124829704, 178405961588244985132285746181186892047941648, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7033, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7032 : B7032.tree = HexagonCover.NBand.M8300_8500.SplitData.node7032 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7033
  · rfl
  · rfl

def B7031 : Block := .branch 147 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866596010411964861129973768, 98320, 393248, 4489733029902317153116643007429569026487448814223424] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7032, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1407).pointIds 1407)]
theorem treeEq7031 : B7031.tree = HexagonCover.NBand.M8300_8500.SplitData.node7031 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7032
  · rfl
  · rfl

def B7030 : Block := .branch 170 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866596010411964861129973768, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7031]
theorem treeEq7030 : B7030.tree = HexagonCover.NBand.M8300_8500.SplitData.node7030 := by
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
  · exact treeEq7031

theorem accepted7030 : B7030.accepted = true := by decide +kernel
theorem checked7030 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7030 (maskNeeds ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866596010411964861129973768, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq7030]
  exact B7030.sound accepted7030
#print axioms checked7030

def B7057 : Block := .branch 138 ![385, 1538, 6148, 79228171958997303332834402312, 100353353393387804136910732226917626777010192, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 1434).pointIds 1434), (.leaf 4 (Common.fact 1426).pointIds 1426), (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1427).pointIds 1427)]
theorem treeEq7057 : B7057.tree = HexagonCover.NBand.M8300_8500.SplitData.node7057 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7056 : Block := .branch 143 ![385, 1538, 6148, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 2993886104105022067471815874865786482706129475862592] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7057, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1433).pointIds 1433)]
theorem treeEq7056 : B7056.tree = HexagonCover.NBand.M8300_8500.SplitData.node7056 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7057
  · rfl
  · rfl

def B7055 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1432).pointIds 1432), (.leaf 5 (Common.fact 774).pointIds 774), B7056]
theorem treeEq7055 : B7055.tree = HexagonCover.NBand.M8300_8500.SplitData.node7055 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7056

def B7054 : Block := .branch 165 ![385, 1538, 6148, 79228171958997303332834402312, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1421).pointIds 1421), B7055, (.leaf 0 [] 0)]
theorem treeEq7054 : B7054.tree = HexagonCover.NBand.M8300_8500.SplitData.node7054 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7055
  · rfl

def B7053 : Block := .branch 167 ![385, 1538, 6148, 79228171958997303332834402312, 2943698366206042254682714811989583718789513232, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1420).pointIds 1420), B7054, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7053 : B7053.tree = HexagonCover.NBand.M8300_8500.SplitData.node7053 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7054
  · rfl

def B7052 : Block := .branch 151 ![385, 1538, 6148, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 2993886104105021735164816928636818256754364405776448] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7053, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1419).pointIds 1419)]
theorem treeEq7052 : B7052.tree = HexagonCover.NBand.M8300_8500.SplitData.node7052 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7053
  · rfl
  · rfl

def B7051 : Block := .branch 97 ![385, 1538, 6148, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 2993886104105021735164658472311789728079177317875776] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 1431).pointIds 1431), (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B7052]
theorem treeEq7051 : B7051.tree = HexagonCover.NBand.M8300_8500.SplitData.node7051 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7052

def B7050 : Block := .branch 133 ![385, 1538, 6148, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 2993886104094132699423188441480961740641360735109184] ![(.leaf 0 (Common.fact 1412).pointIds 1412), (.leaf 1 (Common.fact 1413).pointIds 1413), (.leaf 2 (Common.fact 1414).pointIds 1414), (.leaf 3 (Common.fact 1415).pointIds 1415), (.leaf 4 (Common.fact 1416).pointIds 1416), (.leaf 5 (Common.fact 1417).pointIds 1417), B7051]
theorem treeEq7050 : B7050.tree = HexagonCover.NBand.M8300_8500.SplitData.node7050 := by
  change Tree.branch (133 : Fin 177) _ = Tree.branch (133 : Fin 177) _
  apply congrArg (Tree.branch (133 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7051

def B7049 : Block := .branch 159 ![374144419156711147060143317175958748842277436653953, 146437906389534210, 6148, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 2993155353275467247964086599064603599131532768837696] ![(.leaf 0 (Common.fact 1390).pointIds 1390), (.leaf 1 (Common.fact 1391).pointIds 1391), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B7050]
theorem treeEq7049 : B7049.tree = HexagonCover.NBand.M8300_8500.SplitData.node7049 := by
  change Tree.branch (159 : Fin 177) _ = Tree.branch (159 : Fin 177) _
  apply congrArg (Tree.branch (159 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7050

def B7048 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 2999001359824796176548884478058960346438397620387904] ![B7049, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1411).pointIds 1411)]
theorem treeEq7048 : B7048.tree = HexagonCover.NBand.M8300_8500.SplitData.node7048 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7049
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7047 : Block := .branch 162 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228171958997303332834402312, 267608942382367477698428619271780338071863312, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1410).pointIds 1410), (.leaf 5 (Common.fact 358).pointIds 358), B7048]
theorem treeEq7047 : B7047.tree = HexagonCover.NBand.M8300_8500.SplitData.node7047 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7048

def B7046 : Block := .branch 146 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 79228171958997303332834402312, 178405961588244985132285746181186892047941648, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7047, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7046 : B7046.tree = HexagonCover.NBand.M8300_8500.SplitData.node7046 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7047
  · rfl
  · rfl

def B7045 : Block := .branch 147 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866586565678999121839546376, 98320, 393248, 4489733029902317153116643007429569026487448814223424] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7046, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1407).pointIds 1407)]
theorem treeEq7045 : B7045.tree = HexagonCover.NBand.M8300_8500.SplitData.node7045 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7046
  · rfl
  · rfl

def B7044 : Block := .branch 170 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866586565678999121839546376, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7045]
theorem treeEq7044 : B7044.tree = HexagonCover.NBand.M8300_8500.SplitData.node7044 := by
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
  · exact treeEq7045

theorem accepted7044 : B7044.accepted = true := by decide +kernel
theorem checked7044 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7044 (maskNeeds ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866586565678999121839546376, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq7044]
  exact B7044.sound accepted7044
#print axioms checked7044

def B7073 : Block := .branch 120 ![385, 1538, 6148, 24584, 11150372599265311570767859136324180753088528, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1449).pointIds 1449)]
theorem treeEq7073 : B7073.tree = HexagonCover.NBand.M8300_8500.SplitData.node7073 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7072 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7073, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1448).pointIds 1448)]
theorem treeEq7072 : B7072.tree = HexagonCover.NBand.M8300_8500.SplitData.node7072 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7073
  · rfl
  · rfl

def B7071 : Block := .branch 144 ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B7072, (.leaf 6 (Common.fact 1447).pointIds 1447)]
theorem treeEq7071 : B7071.tree = HexagonCover.NBand.M8300_8500.SplitData.node7071 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7072
  · rfl

def B7070 : Block := .branch 147 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7071, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1446).pointIds 1446)]
theorem treeEq7070 : B7070.tree = HexagonCover.NBand.M8300_8500.SplitData.node7070 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7071
  · rfl
  · rfl

def B7069 : Block := .branch 148 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7070, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1445).pointIds 1445)]
theorem treeEq7069 : B7069.tree = HexagonCover.NBand.M8300_8500.SplitData.node7069 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7070
  · rfl
  · rfl

def B7068 : Block := .branch 149 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 1365).pointIds 1365), (.leaf 1 (Common.fact 1366).pointIds 1366), (.leaf 2 (Common.fact 1367).pointIds 1367), (.leaf 3 (Common.fact 1368).pointIds 1368), B7069, (.leaf 5 (Common.fact 1369).pointIds 1369), (.leaf 6 (Common.fact 1444).pointIds 1444)]
theorem treeEq7068 : B7068.tree = HexagonCover.NBand.M8300_8500.SplitData.node7068 := by
  change Tree.branch (149 : Fin 177) _ = Tree.branch (149 : Fin 177) _
  apply congrArg (Tree.branch (149 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7069
  · rfl
  · rfl

def B7067 : Block := .branch 150 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7068, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1443).pointIds 1443)]
theorem treeEq7067 : B7067.tree = HexagonCover.NBand.M8300_8500.SplitData.node7067 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7068
  · rfl
  · rfl

def B7066 : Block := .branch 66 ![385, 1538, 18907912675552290412548, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 148).pointIds 148), B7067, (.leaf 2 (Common.fact 1041).pointIds 1041), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1442).pointIds 1442)]
theorem treeEq7066 : B7066.tree = HexagonCover.NBand.M8300_8500.SplitData.node7066 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7067
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7065 : Block := .branch 74 ![385, 1538, 18446744073709557764, 243468143406334309424960559407112, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), B7066, (.leaf 3 (Common.fact 1037).pointIds 1037), (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7065 : B7065.tree = HexagonCover.NBand.M8300_8500.SplitData.node7065 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7066
  · rfl
  · rfl
  · rfl
  · rfl

def B7064 : Block := .branch 107 ![385, 1538, 18446744073709557764, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B7065, (.leaf 4 (Common.fact 1362).pointIds 1362), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1441).pointIds 1441)]
theorem treeEq7064 : B7064.tree = HexagonCover.NBand.M8300_8500.SplitData.node7064 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7065
  · rfl
  · rfl
  · rfl

def B7063 : Block := .branch 73 ![385, 1538, 18446744073709557764, 332388207812806089171985147619205128, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B7064, (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7063 : B7063.tree = HexagonCover.NBand.M8300_8500.SplitData.node7063 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7064
  · rfl
  · rfl
  · rfl
  · rfl

def B7062 : Block := .branch 118 ![385, 1538, 18446744073709557764, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B7063, (.leaf 4 (Common.fact 1360).pointIds 1360), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1440).pointIds 1440)]
theorem treeEq7062 : B7062.tree = HexagonCover.NBand.M8300_8500.SplitData.node7062 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7063
  · rfl
  · rfl
  · rfl

def B7061 : Block := .branch 128 ![385, 1538, 18446744073709557764, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B7062, (.leaf 4 (Common.fact 1358).pointIds 1358), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1439).pointIds 1439)]
theorem treeEq7061 : B7061.tree = HexagonCover.NBand.M8300_8500.SplitData.node7061 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7062
  · rfl
  · rfl
  · rfl

def B7060 : Block := .branch 151 ![385, 1538, 18446744073709557764, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7061, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1438).pointIds 1438)]
theorem treeEq7060 : B7060.tree = HexagonCover.NBand.M8300_8500.SplitData.node7060 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7061
  · rfl
  · rfl

def B7059 : Block := .branch 68 ![374144419156711147060143317175368453031918731002241, 1538, 18446744073709557764, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325737885914782747852864] ![(.leaf 0 (Common.fact 1436).pointIds 1436), B7060, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1437).pointIds 1437)]
theorem treeEq7059 : B7059.tree = HexagonCover.NBand.M8300_8500.SplitData.node7059 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7060
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7058 : Block := .branch 168 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325737885914782747852864] ![B7059, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1435).pointIds 1435)]
theorem treeEq7058 : B7058.tree = HexagonCover.NBand.M8300_8500.SplitData.node7058 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7059
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted7058 : B7058.accepted = true := by decide +kernel
theorem checked7058 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7058 (maskNeeds ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325737885914782747852864]) := by
  rw [← treeEq7058]
  exact B7058.sound accepted7058
#print axioms checked7058

def Tip6358_6362 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6362 ![590295810358705652097, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] checked6362
def Tip6358_7030 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7030 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866596010411964861129973768, 98320, 393248, 2993155353275472564876069738728095214359773890216000] checked7030
def Tip6358_7044 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7044 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866586565678999121839546376, 98320, 393248, 2993155353275472564876069738728095214359773890216000] checked7044
def Tip6358_7058 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7058 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325737885914782747852864] checked7058
def B7029 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 11150372599265311570767859136324180753088528, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7029 : B7029.tree = HexagonCover.NBand.M8300_8500.SplitData.node7029 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7028 : Block := .branch 143 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7029, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1404).pointIds 1404)]
theorem treeEq7028 : B7028.tree = HexagonCover.NBand.M8300_8500.SplitData.node7028 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7029
  · rfl
  · rfl

def B7027 : Block := .branch 144 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B7028, (.leaf 6 (Common.fact 1403).pointIds 1403)]
theorem treeEq7027 : B7027.tree = HexagonCover.NBand.M8300_8500.SplitData.node7027 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7028
  · rfl

def B7026 : Block := .branch 147 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B7027, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1402).pointIds 1402)]
theorem treeEq7026 : B7026.tree = HexagonCover.NBand.M8300_8500.SplitData.node7026 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7027
  · rfl
  · rfl

def B7025 : Block := .branch 148 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B7026, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1401).pointIds 1401)]
theorem treeEq7025 : B7025.tree = HexagonCover.NBand.M8300_8500.SplitData.node7025 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7026
  · rfl
  · rfl

def B7024 : Block := .branch 149 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1365).pointIds 1365), (.leaf 1 (Common.fact 1366).pointIds 1366), (.leaf 2 (Common.fact 1367).pointIds 1367), (.leaf 3 (Common.fact 1368).pointIds 1368), B7025, (.leaf 5 (Common.fact 1369).pointIds 1369), (.leaf 6 (Common.fact 1400).pointIds 1400)]
theorem treeEq7024 : B7024.tree = HexagonCover.NBand.M8300_8500.SplitData.node7024 := by
  change Tree.branch (149 : Fin 177) _ = Tree.branch (149 : Fin 177) _
  apply congrArg (Tree.branch (149 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7025
  · rfl
  · rfl

def B7023 : Block := .branch 150 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7024, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1399).pointIds 1399)]
theorem treeEq7023 : B7023.tree = HexagonCover.NBand.M8300_8500.SplitData.node7023 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7024
  · rfl
  · rfl

def B7022 : Block := .branch 128 ![385, 1538, 6148, 81129638414606681695789005168648, 2854495385411919762116571938898990272765591568, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B7023, (.leaf 4 (Common.fact 1358).pointIds 1358), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1398).pointIds 1398)]
theorem treeEq7022 : B7022.tree = HexagonCover.NBand.M8300_8500.SplitData.node7022 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7023
  · rfl
  · rfl
  · rfl

def B7021 : Block := .branch 151 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B7022, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1397).pointIds 1397)]
theorem treeEq7021 : B7021.tree = HexagonCover.NBand.M8300_8500.SplitData.node7021 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7022
  · rfl
  · rfl

def B7020 : Block := .branch 78 ![374144419156711147060143317175958748842277436653953, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1395).pointIds 1395), B7021, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 1396).pointIds 1396)]
theorem treeEq7020 : B7020.tree = HexagonCover.NBand.M8300_8500.SplitData.node7020 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7019 : Block := .branch 168 ![590295810358705652097, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325221377080718880407616] ![B7020, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1394).pointIds 1394)]
theorem treeEq7019 : B7019.tree = HexagonCover.NBand.M8300_8500.SplitData.node7019 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7020
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6361 : Block := .branch 66 ![590295810358705652097, 758927455711921666, 23630279158421935626244, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 148).pointIds 148), Tip6358_6362, (.leaf 2 (Common.fact 1041).pointIds 1041), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7019]
theorem treeEq6361 : B6361.tree = HexagonCover.NBand.M8300_8500.SplitData.node6361 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7019

def B6360 : Block := .branch 74 ![590295810358705652097, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), B6361, Tip6358_7030, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq6360 : B6360.tree = HexagonCover.NBand.M8300_8500.SplitData.node6360 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6361
  · rfl
  · rfl
  · rfl
  · rfl

def B6359 : Block := .branch 73 ![590295810358705652097, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B6360, Tip6358_7044, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq6359 : B6359.tree = HexagonCover.NBand.M8300_8500.SplitData.node6359 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6360
  · rfl
  · rfl
  · rfl
  · rfl

def B6358 : Block := .branch 69 ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![B6359, (.leaf 1 (Common.fact 158).pointIds 158), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), Tip6358_7058]
theorem treeEq6358 : B6358.tree = HexagonCover.NBand.M8300_8500.SplitData.node6358 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6359
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6358 : B6358.accepted = true := by decide +kernel
theorem checked6358 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6358 (maskNeeds ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq6358]
  exact B6358.sound accepted6358
#print axioms checked6358

end HexagonCover.NBand.M8300_8500.SplitTree.Run0097
