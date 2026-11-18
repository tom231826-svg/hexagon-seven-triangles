import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0709 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M6900_7100.SplitData.node0709 := by
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

def B0708 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B0709, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M6900_7100.SplitData.node0708 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0709
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0707 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B0708, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M6900_7100.SplitData.node0707 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0708
  · rfl
  · rfl
  · rfl
  · rfl

def B0706 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38695070960633872881049608, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0707, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M6900_7100.SplitData.node0706 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0707
  · rfl
  · rfl
  · rfl
  · rfl

def B0705 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0706, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M6900_7100.SplitData.node0705 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0706
  · rfl
  · rfl
  · rfl

def B0704 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B0705, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M6900_7100.SplitData.node0704 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0705
  · rfl
  · rfl

def B0703 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0704]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M6900_7100.SplitData.node0703 := by
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
  · exact treeEq0704

def B0702 : Block := .branch 166 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B0703, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M6900_7100.SplitData.node0702 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0703
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0701 : Block := .branch 151 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 38695070960633872881049608, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0702, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M6900_7100.SplitData.node0701 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0702
  · rfl

def B0713 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M6900_7100.SplitData.node0713 := by
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

def B0712 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0713, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M6900_7100.SplitData.node0712 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0713
  · rfl
  · rfl

def B0711 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0712]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M6900_7100.SplitData.node0711 := by
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
  · exact treeEq0712

def B0717 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M6900_7100.SplitData.node0717 := by
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

def B0716 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0717, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M6900_7100.SplitData.node0716 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0717
  · rfl
  · rfl

def B0715 : Block := .branch 159 ![748288838313443577345109768609186252568290935177601, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0716]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M6900_7100.SplitData.node0715 := by
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
  · exact treeEq0716

def B0719 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M6900_7100.SplitData.node0719 := by
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

def B0718 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0719, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M6900_7100.SplitData.node0718 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0719
  · rfl
  · rfl

def B0714 : Block := .branch 124 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0715, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0718]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M6900_7100.SplitData.node0714 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0715
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0718

def B0710 : Block := .branch 90 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0711, B0714, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M6900_7100.SplitData.node0710 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0711
  · exact treeEq0714
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0700 : Block := .branch 119 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0701, (.leaf 5 (Common.fact 163).pointIds 163), B0710]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M6900_7100.SplitData.node0700 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0701
  · rfl
  · exact treeEq0710

theorem accepted0700 : B0700.accepted = true := by decide +kernel
theorem checked0700 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0700 (maskNeeds ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0700]
  exact B0700.sound accepted0700
#print axioms checked0700

def Tip0664_0673 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0673 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] HexagonCover.NBand.M6900_7100.SplitTree.Run0007.checked0673
def Tip0664_0700 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0700 ![748288838313422309697177209955219791655326449664385, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked0700
def B0671 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M6900_7100.SplitData.node0671 := by
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

def B0670 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0671, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M6900_7100.SplitData.node0670 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0671
  · rfl
  · rfl

def B0669 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0670]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M6900_7100.SplitData.node0669 := by
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
  · exact treeEq0670

def B0694 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M6900_7100.SplitData.node0694 := by
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

def B0693 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0694, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M6900_7100.SplitData.node0693 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0694
  · rfl
  · rfl

def B0672 : Block := .branch 112 ![748288838313422304504880351420982458935188826096001, 619574925346413914615711234, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip0664_0673, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0693]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M6900_7100.SplitData.node0672 := by
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
  · exact treeEq0693

def B0668 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 618970462436606600028358146, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0669, B0672, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M6900_7100.SplitData.node0668 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0669
  · exact treeEq0672
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0698 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M6900_7100.SplitData.node0698 := by
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

def B0697 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0698, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M6900_7100.SplitData.node0697 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0698
  · rfl
  · rfl

def B0696 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0697]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M6900_7100.SplitData.node0696 := by
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
  · exact treeEq0697

def B0721 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M6900_7100.SplitData.node0721 := by
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

def B0720 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0721, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M6900_7100.SplitData.node0720 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0721
  · rfl
  · rfl

def B0699 : Block := .branch 112 ![748288838313422304504880351420392163124830120444289, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![Tip0664_0700, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0720]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M6900_7100.SplitData.node0699 := by
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
  · exact treeEq0720

def B0695 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 618971052732416958734009858, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0696, B0699, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M6900_7100.SplitData.node0695 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0696
  · exact treeEq0699
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0667 : Block := .branch 69 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 7120443212451886929924, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0668, B0695, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M6900_7100.SplitData.node0667 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0668
  · exact treeEq0695
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0666 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0667, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M6900_7100.SplitData.node0666 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0667
  · rfl
  · rfl

def B0665 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 618970462436606600028358146, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0666, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M6900_7100.SplitData.node0665 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0666
  · rfl

def B0664 : Block := .branch 169 ![10387129018270111715863986064851329, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B0665, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M6900_7100.SplitData.node0664 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0664 : B0664.accepted = true := by decide +kernel
theorem checked0664 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0664 (maskNeeds ![10387129018270111715863986064851329, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0664]
  exact B0664.sound accepted0664
#print axioms checked0664

def Tip0649_0664 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0664 ![10387129018270111715863986064851329, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] checked0664
def B0663 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 486).pointIds 486), (.leaf 1 (Common.fact 487).pointIds 487), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M6900_7100.SplitData.node0663 := by
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

def B0662 : Block := .branch 159 ![748288838313443561768219193004703366976801947517313, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 484).pointIds 484), B0663, (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 485).pointIds 485)]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M6900_7100.SplitData.node0662 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0663
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0661 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![B0662, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 483).pointIds 483)]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M6900_7100.SplitData.node0661 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0662
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0660 : Block := .branch 161 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38695070960633872881049608, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B0661, (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M6900_7100.SplitData.node0660 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0661
  · rfl
  · rfl
  · rfl
  · rfl

def B0659 : Block := .branch 137 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38695070960633872881049608, 5847433797016317632695797616834581573760113016848, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B0660, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M6900_7100.SplitData.node0659 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0660
  · rfl
  · rfl
  · rfl

def B0658 : Block := .branch 162 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 754).pointIds 754), B0659, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M6900_7100.SplitData.node0658 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · rfl
  · rfl

def B0657 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38695070960633872881049608, 1427247692706284399611944396176278292403421200, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 481).pointIds 481), (.leaf 5 (Common.fact 482).pointIds 482), B0658]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M6900_7100.SplitData.node0657 := by
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
  · exact treeEq0658

def B0656 : Block := .branch 150 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 38695070960633872881049608, 324518553658426726783156020674576, 2854495427947215627233879871820816201736912928, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0657, (.leaf 5 (Common.fact 476).pointIds 476), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M6900_7100.SplitData.node0656 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0657
  · rfl
  · rfl

def B0655 : Block := .branch 125 ![841824943102600080887857764845035478124810551165313, 1099511629314, 6148, 38695070960633872881049608, 324518553658426726783156020674576, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 475).pointIds 475), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0656, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M6900_7100.SplitData.node0655 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0656
  · rfl

def B0654 : Block := .branch 169 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144424753675518176056541098525785438169291292736] ![B0655, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M6900_7100.SplitData.node0654 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0655
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0653 : Block := .branch 142 ![93536104789177786767571130494298572060973089161601, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B0654]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M6900_7100.SplitData.node0653 := by
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
  · exact treeEq0654

def B0652 : Block := .branch 166 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B0653, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M6900_7100.SplitData.node0652 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0653
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0651 : Block := .branch 151 ![2535301200456458802993406411137, 936749822004692482, 18482772870728521732, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B0652, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M6900_7100.SplitData.node0651 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0652
  · rfl

def B0650 : Block := .branch 108 ![10387129018270111715863986064851329, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B0651, (.leaf 5 (Common.fact 322).pointIds 322), Tip0649_0664]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M6900_7100.SplitData.node0650 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0651
  · rfl
  · rfl

def B0726 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M6900_7100.SplitData.node0726 := by
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

def B0725 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0726, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M6900_7100.SplitData.node0725 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0726
  · rfl
  · rfl

def B0724 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B0725, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M6900_7100.SplitData.node0724 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0725
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0723 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0724, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M6900_7100.SplitData.node0723 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0724
  · rfl

def B0722 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0723, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M6900_7100.SplitData.node0722 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0649 : Block := .branch 101 ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0650, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B0722]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M6900_7100.SplitData.node0649 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0650
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0722

theorem accepted0649 : B0649.accepted = true := by decide +kernel
theorem checked0649 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0649 (maskNeeds ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0649]
  exact B0649.sound accepted0649
#print axioms checked0649

def Tip0647_0649 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0649 ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0649
def B0731 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M6900_7100.SplitData.node0731 := by
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

def B0730 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B0731, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M6900_7100.SplitData.node0730 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0731
  · rfl
  · rfl

def B0729 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218543403231594674788036628713046080] ![B0730, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M6900_7100.SplitData.node0729 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0730
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0728 : Block := .branch 151 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0729, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M6900_7100.SplitData.node0728 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0729
  · rfl

def B0727 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 374144419178489218543403231594674788036628713046080] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0728, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M6900_7100.SplitData.node0727 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0728
  · rfl
  · rfl

def B0648 : Block := .branch 91 ![10384593717069655257060992658440577, 618970463301297728483493378, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip0647_0649, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B0727]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M6900_7100.SplitData.node0648 := by
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
  · exact treeEq0727

def B0741 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441889030543861336302778395099922496] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0741 : B0741.tree = HexagonCover.NBand.M6900_7100.SplitData.node0741 := by
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

def B0740 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0741, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0740 : B0740.tree = HexagonCover.NBand.M6900_7100.SplitData.node0740 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0741
  · rfl

def B0739 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030853346346124123463824703552] ![B0740, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq0739 : B0739.tree = HexagonCover.NBand.M6900_7100.SplitData.node0739 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0740
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0738 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B0739]
theorem treeEq0738 : B0738.tree = HexagonCover.NBand.M6900_7100.SplitData.node0738 := by
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
  · exact treeEq0739

def B0737 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B0738, (.leaf 0 [] 0)]
theorem treeEq0737 : B0737.tree = HexagonCover.NBand.M6900_7100.SplitData.node0737 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0738
  · rfl

def B0736 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B0737, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M6900_7100.SplitData.node0736 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0737
  · rfl

def B0735 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0736, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M6900_7100.SplitData.node0735 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0736
  · rfl
  · rfl

def B0734 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374684615859966216364359744] ![B0735, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M6900_7100.SplitData.node0734 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0735
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0733 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B0734, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M6900_7100.SplitData.node0733 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0734
  · rfl

def B0732 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 756).pointIds 756), (.leaf 3 (Common.fact 757).pointIds 757), B0733, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M6900_7100.SplitData.node0732 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0733
  · rfl
  · rfl

def B0647 : Block := .branch 89 ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B0648, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0732]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M6900_7100.SplitData.node0647 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0648
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0732

theorem accepted0647 : B0647.accepted = true := by decide +kernel
theorem checked0647 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0647 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0647]
  exact B0647.sound accepted0647
#print axioms checked0647

end HexagonCover.NBand.M6900_7100.SplitTree.Run0008
