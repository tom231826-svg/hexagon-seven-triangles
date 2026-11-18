import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0011
import HexagonCover.NBand.M8300_8500.SplitTree.Run0014
import HexagonCover.NBand.M8300_8500.SplitTree.Run0015
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0906_1069 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1069 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0014.checked1069
def Tip0906_1143 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1143 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0015.checked1143
def Tip0906_0907 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0907 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0015.checked0907
def B1141 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1141 : B1141.tree = HexagonCover.NBand.M8300_8500.SplitData.node1141 := by
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

def B1140 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1141, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M8300_8500.SplitData.node1140 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1141
  · rfl

def B1139 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 237713501762463763880824823816, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1140]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M8300_8500.SplitData.node1139 := by
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
  · exact treeEq1140

def B1068 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip0906_1069, B1139, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1068 : B1068.tree = HexagonCover.NBand.M8300_8500.SplitData.node1068 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1139
  · rfl
  · rfl
  · rfl

def B1215 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1215 : B1215.tree = HexagonCover.NBand.M8300_8500.SplitData.node1215 := by
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

def B1214 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1215, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1214 : B1214.tree = HexagonCover.NBand.M8300_8500.SplitData.node1214 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1215
  · rfl

def B1213 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 237713501762463763880824823816, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 862).pointIds 862), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1214]
theorem treeEq1213 : B1213.tree = HexagonCover.NBand.M8300_8500.SplitData.node1213 := by
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
  · exact treeEq1214

def B1142 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip0906_1143, B1213, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1142 : B1142.tree = HexagonCover.NBand.M8300_8500.SplitData.node1142 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1213
  · rfl
  · rfl
  · rfl

def B1067 : Block := .branch 78 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B1068, B1142, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1067 : B1067.tree = HexagonCover.NBand.M8300_8500.SplitData.node1067 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1068
  · exact treeEq1142
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1224 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq1224 : B1224.tree = HexagonCover.NBand.M8300_8500.SplitData.node1224 := by
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

def B1223 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B1224, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1223 : B1223.tree = HexagonCover.NBand.M8300_8500.SplitData.node1223 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1224
  · rfl
  · rfl

def B1222 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B1223, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1222 : B1222.tree = HexagonCover.NBand.M8300_8500.SplitData.node1222 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1223
  · rfl
  · rfl

def B1221 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B1222, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1221 : B1221.tree = HexagonCover.NBand.M8300_8500.SplitData.node1221 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1222
  · rfl
  · rfl

def B1220 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1221, (.leaf 0 [] 0)]
theorem treeEq1220 : B1220.tree = HexagonCover.NBand.M8300_8500.SplitData.node1220 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1221
  · rfl

def B1219 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1220, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1219 : B1219.tree = HexagonCover.NBand.M8300_8500.SplitData.node1219 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1220
  · rfl

def B1218 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B1219, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1218 : B1218.tree = HexagonCover.NBand.M8300_8500.SplitData.node1218 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1219
  · rfl
  · rfl

def B1217 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), B1218, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1217 : B1217.tree = HexagonCover.NBand.M8300_8500.SplitData.node1217 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1218
  · rfl
  · rfl
  · rfl

def B1216 : Block := .branch 161 ![604463488519866704462209, 151152620940525821756930, 4949040074047388183959556, 79237833920821254626941624328, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 864).pointIds 864), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B1217]
theorem treeEq1216 : B1216.tree = HexagonCover.NBand.M8300_8500.SplitData.node1216 := by
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
  · exact treeEq1217

def B1066 : Block := .branch 76 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), B1067, B1216, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1066 : B1066.tree = HexagonCover.NBand.M8300_8500.SplitData.node1066 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1067
  · exact treeEq1216
  · rfl
  · rfl
  · rfl
  · rfl

def B0906 : Block := .branch 68 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0906_0907, B1066, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0906 : B0906.tree = HexagonCover.NBand.M8300_8500.SplitData.node0906 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1066
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0906 : B0906.accepted = true := by decide +kernel
theorem checked0906 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0906 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0906]
  exact B0906.sound accepted0906
#print axioms checked0906

def Tip0033_0036 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0036 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0011.checked0036
def Tip0033_0865 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0865 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0011.checked0865
def Tip0033_0880 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0880 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0011.checked0880
def B0864 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 43598678261745240631244871577195302486048, 374144430307083746325456125883266874736924138405952] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 753).pointIds 753), (.leaf 5 (Common.fact 520).pointIds 520), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0864 : B0864.tree = HexagonCover.NBand.M8300_8500.SplitData.node0864 := by
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

def B0863 : Block := .branch 168 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 43598678261745240631244871577195302486048, 11150372599265312808707898421705005407404096] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 748).pointIds 748), (.leaf 5 (Common.fact 515).pointIds 515), B0864]
theorem treeEq0863 : B0863.tree = HexagonCover.NBand.M8300_8500.SplitData.node0863 := by
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
  · exact treeEq0864

def B0862 : Block := .branch 97 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 1329227995784915872903807060280442896, 43598678261745240631244871577195302486048, 11172171938396185429023520857493603058450496] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B0863, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0862 : B0862.tree = HexagonCover.NBand.M8300_8500.SplitData.node0862 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0863
  · rfl
  · rfl
  · rfl

def B0861 : Block := .branch 107 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 1329227995784915872903807060280442896, 43598678261745240631244871577195302486048, 11172177255308168568687012472721844179828800] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B0862, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0861 : B0861.tree = HexagonCover.NBand.M8300_8500.SplitData.node0861 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0862
  · rfl
  · rfl
  · rfl

def B0860 : Block := .branch 120 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 98320, 43598678261745240631244871577195302486048, 11172177255308168568687012472721844179828800] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0861, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 801).pointIds 801)]
theorem treeEq0860 : B0860.tree = HexagonCover.NBand.M8300_8500.SplitData.node0860 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0861
  · rfl
  · rfl

def B0859 : Block := .branch 125 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 98320, 43556142965880123323311949751266331459616, 11172177255308168568687012472721844179828800] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B0860, (.leaf 6 (Common.fact 800).pointIds 800)]
theorem treeEq0859 : B0859.tree = HexagonCover.NBand.M8300_8500.SplitData.node0859 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0860
  · rfl

def B0858 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 98320, 393248, 11172177255308168568687012472721844179828800] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0859, (.leaf 6 (Common.fact 799).pointIds 799)]
theorem treeEq0858 : B0858.tree = HexagonCover.NBand.M8300_8500.SplitData.node0858 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0859
  · rfl

def B0857 : Block := .branch 143 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 2787593149816327892691964784081045188345872, 393248, 21804656042856997919153336397663426838592] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 798).pointIds 798), (.leaf 5 (Common.fact 217).pointIds 217), B0858]
theorem treeEq0857 : B0857.tree = HexagonCover.NBand.M8300_8500.SplitData.node0857 := by
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
  · exact treeEq0858

def B0856 : Block := .branch 141 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 98320, 393248, 21804656042856997919153336397663426838592] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), B0857, (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq0856 : B0856.tree = HexagonCover.NBand.M8300_8500.SplitData.node0856 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0857
  · rfl
  · rfl

def B0855 : Block := .branch 150 ![604463488519866704462209, 151152620940525821756930, 53230514994906640848787460, 24584, 98320, 393248, 21804656042856997919153336397663426838592] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B0856, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 791).pointIds 791)]
theorem treeEq0855 : B0855.tree = HexagonCover.NBand.M8300_8500.SplitData.node0855 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0856
  · rfl
  · rfl

def B0035 : Block := .branch 90 ![604463488519866704462209, 151152765055713897612802, 53230514994906640848787460, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![Tip0033_0036, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B0855]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M8300_8500.SplitData.node0035 := by
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
  · exact treeEq0855

def B0034 : Block := .branch 85 ![604463488519866704462209, 151152765055713897612802, 33887701881072574053488644, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B0035, Tip0033_0865, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M8300_8500.SplitData.node0034 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0035
  · rfl
  · rfl
  · rfl
  · rfl

def B0033 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 14544888767238507258189828, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B0034, Tip0033_0880, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M8300_8500.SplitData.node0033 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0034
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0033 : B0033.accepted = true := by decide +kernel
theorem checked0033 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0033 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 14544888767238507258189828, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0033]
  exact B0033.sound accepted0033
#print axioms checked0033

def B1259 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M8300_8500.SplitData.node1259 := by
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

def B1258 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1259, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1258 : B1258.tree = HexagonCover.NBand.M8300_8500.SplitData.node1258 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1259
  · rfl
  · rfl

def B1257 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1258, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1257 : B1257.tree = HexagonCover.NBand.M8300_8500.SplitData.node1257 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1258
  · rfl
  · rfl

def B1256 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1257, (.leaf 0 [] 0)]
theorem treeEq1256 : B1256.tree = HexagonCover.NBand.M8300_8500.SplitData.node1256 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1257
  · rfl

def B1255 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1256, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1255 : B1255.tree = HexagonCover.NBand.M8300_8500.SplitData.node1255 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1256
  · rfl

def B1254 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1255, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1254 : B1254.tree = HexagonCover.NBand.M8300_8500.SplitData.node1254 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1255
  · rfl
  · rfl

def B1253 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1254, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq1253 : B1253.tree = HexagonCover.NBand.M8300_8500.SplitData.node1253 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1254
  · rfl
  · rfl
  · rfl

def B1252 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 42535295865117307932921825928971419680, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B1253]
theorem treeEq1252 : B1252.tree = HexagonCover.NBand.M8300_8500.SplitData.node1252 := by
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
  · exact treeEq1253

def B1266 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M8300_8500.SplitData.node1266 := by
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

def B1265 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1266, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M8300_8500.SplitData.node1265 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1266
  · rfl
  · rfl

def B1264 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1265, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M8300_8500.SplitData.node1264 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1265
  · rfl
  · rfl

def B1263 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1264, (.leaf 0 [] 0)]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M8300_8500.SplitData.node1263 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1264
  · rfl

def B1262 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1263, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M8300_8500.SplitData.node1262 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1263
  · rfl

def B1261 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1262, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M8300_8500.SplitData.node1261 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1262
  · rfl
  · rfl

def B1260 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1261, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M8300_8500.SplitData.node1260 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1261
  · rfl
  · rfl
  · rfl

def B1251 : Block := .branch 125 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B1252, B1260]
theorem treeEq1251 : B1251.tree = HexagonCover.NBand.M8300_8500.SplitData.node1251 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1252
  · exact treeEq1260

theorem accepted1251 : B1251.accepted = true := by decide +kernel
theorem checked1251 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1251 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1251]
  exact B1251.sound accepted1251
#print axioms checked1251

def B1293 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq1293 : B1293.tree = HexagonCover.NBand.M8300_8500.SplitData.node1293 := by
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

def B1292 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1293, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1292 : B1292.tree = HexagonCover.NBand.M8300_8500.SplitData.node1292 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1293
  · rfl
  · rfl

def B1291 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1292, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1291 : B1291.tree = HexagonCover.NBand.M8300_8500.SplitData.node1291 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1292
  · rfl
  · rfl

def B1290 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1291, (.leaf 0 [] 0)]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M8300_8500.SplitData.node1290 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1291
  · rfl

def B1289 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1290, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M8300_8500.SplitData.node1289 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl

def B1288 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1289, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M8300_8500.SplitData.node1288 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1289
  · rfl
  · rfl

def B1287 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 4115588610745627273704432248908167034368494568734784] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1288, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M8300_8500.SplitData.node1287 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1288
  · rfl
  · rfl
  · rfl

def B1286 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 42576834239985586553950069899605180448, 3367299772432204979584145614557430128304657106731072] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B1287]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M8300_8500.SplitData.node1286 := by
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
  · exact treeEq1287

def B1300 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1300 : B1300.tree = HexagonCover.NBand.M8300_8500.SplitData.node1300 := by
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

def B1299 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B1300, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1299 : B1299.tree = HexagonCover.NBand.M8300_8500.SplitData.node1299 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1300
  · rfl
  · rfl

def B1298 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B1299, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1298 : B1298.tree = HexagonCover.NBand.M8300_8500.SplitData.node1298 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1299
  · rfl
  · rfl

def B1297 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B1298, (.leaf 0 [] 0)]
theorem treeEq1297 : B1297.tree = HexagonCover.NBand.M8300_8500.SplitData.node1297 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1298
  · rfl

def B1296 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B1297, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1296 : B1296.tree = HexagonCover.NBand.M8300_8500.SplitData.node1296 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1297
  · rfl

def B1295 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B1296, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1295 : B1295.tree = HexagonCover.NBand.M8300_8500.SplitData.node1295 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1296
  · rfl
  · rfl

def B1294 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664613997897293639730362046839021576, 178405964247350013809434345442367324649783312, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1295, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1294 : B1294.tree = HexagonCover.NBand.M8300_8500.SplitData.node1294 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1295
  · rfl
  · rfl
  · rfl

def B1285 : Block := .branch 125 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B1286, B1294]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M8300_8500.SplitData.node1285 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1286
  · exact treeEq1294

theorem accepted1285 : B1285.accepted = true := by decide +kernel
theorem checked1285 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1285 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 664614077125456153994699640382971912, 179799760822258177755780327834407847243907088, 41538374868278621028243970634154016, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1285]
  exact B1285.sound accepted1285
#print axioms checked1285

end HexagonCover.NBand.M8300_8500.SplitTree.Run0016
