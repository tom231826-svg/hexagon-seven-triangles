import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0058
import HexagonCover.NBand.M8300_8500.SplitTree.Run0059
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0060
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4125_4128 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4128 ![2251799813685633, 504474076765488642, 4873482246350270879504388, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0058.checked4128
def Tip4125_4210 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4210 ![2251799813685633, 360358888689632770, 37778967891754180679684, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0058.checked4210
def Tip4125_4234 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4234 ![2251799813685633, 377789678988460306728450, 37778967891754180679684, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0058.checked4234
def B4209 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq4209 : B4209.tree = HexagonCover.NBand.M8300_8500.SplitData.node4209 := by
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

def B4208 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B4209, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4208 : B4208.tree = HexagonCover.NBand.M8300_8500.SplitData.node4208 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4209
  · rfl
  · rfl

def B4207 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B4208, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4207 : B4207.tree = HexagonCover.NBand.M8300_8500.SplitData.node4207 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4208
  · rfl
  · rfl

def B4206 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B4207, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4206 : B4206.tree = HexagonCover.NBand.M8300_8500.SplitData.node4206 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4207
  · rfl
  · rfl

def B4205 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4206, (.leaf 0 [] 0)]
theorem treeEq4205 : B4205.tree = HexagonCover.NBand.M8300_8500.SplitData.node4205 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4206
  · rfl

def B4204 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4205, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4204 : B4204.tree = HexagonCover.NBand.M8300_8500.SplitData.node4204 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4205
  · rfl

def B4203 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B4204, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4203 : B4203.tree = HexagonCover.NBand.M8300_8500.SplitData.node4203 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4204
  · rfl
  · rfl

def B4202 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4203, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4202 : B4202.tree = HexagonCover.NBand.M8300_8500.SplitData.node4202 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4203
  · rfl
  · rfl
  · rfl

def B4201 : Block := .branch 161 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4202]
theorem treeEq4201 : B4201.tree = HexagonCover.NBand.M8300_8500.SplitData.node4201 := by
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
  · exact treeEq4202

def B4127 : Block := .branch 83 ![2251799813685633, 504474076765488642, 4873482246350270879504388, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip4125_4128, B4201, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq4127 : B4127.tree = HexagonCover.NBand.M8300_8500.SplitData.node4127 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4201
  · rfl
  · rfl
  · rfl

def B4126 : Block := .branch 82 ![2251799813685633, 504474076765488642, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B4127, Tip4125_4210, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq4126 : B4126.tree = HexagonCover.NBand.M8300_8500.SplitData.node4126 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4127
  · rfl
  · rfl
  · rfl
  · rfl

def B4125 : Block := .branch 78 ![2251799813685633, 75558368199991088907778, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B4126, Tip4125_4234, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4125 : B4125.tree = HexagonCover.NBand.M8300_8500.SplitData.node4125 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4126
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4125 : B4125.accepted = true := by decide +kernel
theorem checked4125 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4125 (maskNeeds ![2251799813685633, 75558368199991088907778, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4125]
  exact B4125.sound accepted4125
#print axioms checked4125

def Tip4124_4249 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4249 ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0059.checked4249
def Tip4124_4331 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4331 ![2251799813685633, 360358888689632770, 113336831617668504098820, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0059.checked4331
def Tip4124_4343 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4343 ![2251799813685633, 453384436202522049250818, 113336831617668504098820, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0059.checked4343
def Tip4124_4125 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4125 ![2251799813685633, 75558368199991088907778, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked4125
def B4330 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq4330 : B4330.tree = HexagonCover.NBand.M8300_8500.SplitData.node4330 := by
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

def B4329 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B4330, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4329 : B4329.tree = HexagonCover.NBand.M8300_8500.SplitData.node4329 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4330
  · rfl
  · rfl

def B4328 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B4329, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4328 : B4328.tree = HexagonCover.NBand.M8300_8500.SplitData.node4328 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4329
  · rfl
  · rfl

def B4327 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B4328, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4327 : B4327.tree = HexagonCover.NBand.M8300_8500.SplitData.node4327 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4328
  · rfl
  · rfl

def B4326 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4327, (.leaf 0 [] 0)]
theorem treeEq4326 : B4326.tree = HexagonCover.NBand.M8300_8500.SplitData.node4326 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4327
  · rfl

def B4325 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4326, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4325 : B4325.tree = HexagonCover.NBand.M8300_8500.SplitData.node4325 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4326
  · rfl

def B4324 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B4325, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4324 : B4324.tree = HexagonCover.NBand.M8300_8500.SplitData.node4324 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4325
  · rfl
  · rfl

def B4323 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4324, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4323 : B4323.tree = HexagonCover.NBand.M8300_8500.SplitData.node4323 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4324
  · rfl
  · rfl
  · rfl

def B4322 : Block := .branch 161 ![2251799813685633, 360358888689632770, 113336831617668504098820, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4323]
theorem treeEq4322 : B4322.tree = HexagonCover.NBand.M8300_8500.SplitData.node4322 := by
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
  · exact treeEq4323

def B4248 : Block := .branch 83 ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip4124_4249, B4322, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq4248 : B4248.tree = HexagonCover.NBand.M8300_8500.SplitData.node4248 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4322
  · rfl
  · rfl
  · rfl

def B4247 : Block := .branch 82 ![2251799813685633, 504474076765488642, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B4248, Tip4124_4331, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq4247 : B4247.tree = HexagonCover.NBand.M8300_8500.SplitData.node4247 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4248
  · rfl
  · rfl
  · rfl
  · rfl

def B4246 : Block := .branch 78 ![2251799813685633, 151153125414052831430146, 113336831617668504098820, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B4247, Tip4124_4343, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4246 : B4246.tree = HexagonCover.NBand.M8300_8500.SplitData.node4246 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4247
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4124 : Block := .branch 76 ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip4124_4125, B4246, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq4124 : B4124.tree = HexagonCover.NBand.M8300_8500.SplitData.node4124 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4246
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4124 : B4124.accepted = true := by decide +kernel
theorem checked4124 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4124 (maskNeeds ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4124]
  exact B4124.sound accepted4124
#print axioms checked4124

def B4386 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4386 : B4386.tree = HexagonCover.NBand.M8300_8500.SplitData.node4386 := by
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

def B4385 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4386, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4385 : B4385.tree = HexagonCover.NBand.M8300_8500.SplitData.node4385 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4386
  · rfl
  · rfl
  · rfl

def B4384 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42535295865117307932921825928971419680, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B4385]
theorem treeEq4384 : B4384.tree = HexagonCover.NBand.M8300_8500.SplitData.node4384 := by
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
  · exact treeEq4385

def B4390 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556142965880123323311949751266331459616, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4390 : B4390.tree = HexagonCover.NBand.M8300_8500.SplitData.node4390 := by
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

def B4389 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4390, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4389 : B4389.tree = HexagonCover.NBand.M8300_8500.SplitData.node4389 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4390
  · rfl

def B4388 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4389]
theorem treeEq4388 : B4388.tree = HexagonCover.NBand.M8300_8500.SplitData.node4388 := by
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
  · exact treeEq4389

def B4387 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4388, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4387 : B4387.tree = HexagonCover.NBand.M8300_8500.SplitData.node4387 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4388
  · rfl
  · rfl
  · rfl

def B4383 : Block := .branch 125 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4384, B4387]
theorem treeEq4383 : B4383.tree = HexagonCover.NBand.M8300_8500.SplitData.node4383 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4384
  · exact treeEq4387

def B4394 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4394 : B4394.tree = HexagonCover.NBand.M8300_8500.SplitData.node4394 := by
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

def B4393 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4394, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4393 : B4393.tree = HexagonCover.NBand.M8300_8500.SplitData.node4393 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4394
  · rfl
  · rfl
  · rfl

def B4392 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422294120286634350736906063837462396960, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B4393]
theorem treeEq4392 : B4392.tree = HexagonCover.NBand.M8300_8500.SplitData.node4392 := by
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
  · exact treeEq4393

def B4391 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4392, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4391 : B4391.tree = HexagonCover.NBand.M8300_8500.SplitData.node4391 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4392
  · rfl

def B4382 : Block := .branch 121 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4383, (.leaf 5 (Common.fact 256).pointIds 256), B4391]
theorem treeEq4382 : B4382.tree = HexagonCover.NBand.M8300_8500.SplitData.node4382 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4383
  · rfl
  · exact treeEq4391

def B4399 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4399 : B4399.tree = HexagonCover.NBand.M8300_8500.SplitData.node4399 := by
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

def B4398 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4399, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4398 : B4398.tree = HexagonCover.NBand.M8300_8500.SplitData.node4398 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4399
  · rfl

def B4397 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4398]
theorem treeEq4397 : B4397.tree = HexagonCover.NBand.M8300_8500.SplitData.node4397 := by
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
  · exact treeEq4398

def B4396 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4397, (.leaf 0 [] 0)]
theorem treeEq4396 : B4396.tree = HexagonCover.NBand.M8300_8500.SplitData.node4396 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4397
  · rfl

def B4395 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4396, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4395 : B4395.tree = HexagonCover.NBand.M8300_8500.SplitData.node4395 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4396
  · rfl

def B4381 : Block := .branch 119 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4382, B4395, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4381 : B4381.tree = HexagonCover.NBand.M8300_8500.SplitData.node4381 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4382
  · exact treeEq4395
  · rfl
  · rfl

theorem accepted4381 : B4381.accepted = true := by decide +kernel
theorem checked4381 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4381 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4381]
  exact B4381.sound accepted4381
#print axioms checked4381

def Tip4380_4381 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4381 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4381
def B4405 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4405 : B4405.tree = HexagonCover.NBand.M8300_8500.SplitData.node4405 := by
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

def B4404 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4405, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4404 : B4404.tree = HexagonCover.NBand.M8300_8500.SplitData.node4404 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4405
  · rfl
  · rfl
  · rfl

def B4403 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B4404]
theorem treeEq4403 : B4403.tree = HexagonCover.NBand.M8300_8500.SplitData.node4403 := by
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
  · exact treeEq4404

def B4409 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4409 : B4409.tree = HexagonCover.NBand.M8300_8500.SplitData.node4409 := by
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

def B4408 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4409, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4408 : B4408.tree = HexagonCover.NBand.M8300_8500.SplitData.node4408 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4409
  · rfl

def B4407 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4408]
theorem treeEq4407 : B4407.tree = HexagonCover.NBand.M8300_8500.SplitData.node4407 := by
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
  · exact treeEq4408

def B4406 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4407, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4406 : B4406.tree = HexagonCover.NBand.M8300_8500.SplitData.node4406 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4407
  · rfl
  · rfl
  · rfl

def B4402 : Block := .branch 125 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4403, B4406]
theorem treeEq4402 : B4402.tree = HexagonCover.NBand.M8300_8500.SplitData.node4402 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4403
  · exact treeEq4406

def B4413 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4413 : B4413.tree = HexagonCover.NBand.M8300_8500.SplitData.node4413 := by
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

def B4412 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4413, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4412 : B4412.tree = HexagonCover.NBand.M8300_8500.SplitData.node4412 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4413
  · rfl
  · rfl
  · rfl

def B4411 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4412]
theorem treeEq4411 : B4411.tree = HexagonCover.NBand.M8300_8500.SplitData.node4411 := by
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
  · exact treeEq4412

def B4410 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4411, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4410 : B4410.tree = HexagonCover.NBand.M8300_8500.SplitData.node4410 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4411
  · rfl

def B4401 : Block := .branch 121 ![2251799813685633, 360358888689632770, 37815861379901599782916, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4402, (.leaf 5 (Common.fact 256).pointIds 256), B4410]
theorem treeEq4401 : B4401.tree = HexagonCover.NBand.M8300_8500.SplitData.node4401 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4402
  · rfl
  · exact treeEq4410

def B4418 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4418 : B4418.tree = HexagonCover.NBand.M8300_8500.SplitData.node4418 := by
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

def B4417 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4418, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4417 : B4417.tree = HexagonCover.NBand.M8300_8500.SplitData.node4417 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4418
  · rfl

def B4416 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4417]
theorem treeEq4416 : B4416.tree = HexagonCover.NBand.M8300_8500.SplitData.node4416 := by
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
  · exact treeEq4417

def B4415 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4416, (.leaf 0 [] 0)]
theorem treeEq4415 : B4415.tree = HexagonCover.NBand.M8300_8500.SplitData.node4415 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4416
  · rfl

def B4414 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4415, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4414 : B4414.tree = HexagonCover.NBand.M8300_8500.SplitData.node4414 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4415
  · rfl

def B4400 : Block := .branch 119 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4401, B4414, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4400 : B4400.tree = HexagonCover.NBand.M8300_8500.SplitData.node4400 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4401
  · exact treeEq4414
  · rfl
  · rfl

def B4380 : Block := .branch 115 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4380_4381, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B4400, (.leaf 0 [] 0)]
theorem treeEq4380 : B4380.tree = HexagonCover.NBand.M8300_8500.SplitData.node4380 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4400
  · rfl

theorem accepted4380 : B4380.accepted = true := by decide +kernel
theorem checked4380 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4380 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4380]
  exact B4380.sound accepted4380
#print axioms checked4380

def Tip4377_4380 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4380 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4380
def B4422 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq4422 : B4422.tree = HexagonCover.NBand.M8300_8500.SplitData.node4422 := by
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

def B4421 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4422, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4421 : B4421.tree = HexagonCover.NBand.M8300_8500.SplitData.node4421 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4422
  · rfl
  · rfl
  · rfl

def B4420 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4421]
theorem treeEq4420 : B4420.tree = HexagonCover.NBand.M8300_8500.SplitData.node4420 := by
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
  · exact treeEq4421

def B4419 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4420, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq4419 : B4419.tree = HexagonCover.NBand.M8300_8500.SplitData.node4419 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4420
  · rfl

def B4379 : Block := .branch 113 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4377_4380, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B4419]
theorem treeEq4379 : B4379.tree = HexagonCover.NBand.M8300_8500.SplitData.node4379 := by
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
  · exact treeEq4419

def B4427 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4427 : B4427.tree = HexagonCover.NBand.M8300_8500.SplitData.node4427 := by
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

def B4426 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4427, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4426 : B4426.tree = HexagonCover.NBand.M8300_8500.SplitData.node4426 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4427
  · rfl

def B4425 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B4426]
theorem treeEq4425 : B4425.tree = HexagonCover.NBand.M8300_8500.SplitData.node4425 := by
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
  · exact treeEq4426

def B4424 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B4425, (.leaf 0 [] 0)]
theorem treeEq4424 : B4424.tree = HexagonCover.NBand.M8300_8500.SplitData.node4424 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4425
  · rfl

def B4423 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B4424, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4423 : B4423.tree = HexagonCover.NBand.M8300_8500.SplitData.node4423 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4424
  · rfl

def B4378 : Block := .branch 108 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B4379, B4423, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq4378 : B4378.tree = HexagonCover.NBand.M8300_8500.SplitData.node4378 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4379
  · exact treeEq4423
  · rfl
  · rfl

def B4431 : Block := .branch 161 ![385, 1538, 37815861379901599782916, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq4431 : B4431.tree = HexagonCover.NBand.M8300_8500.SplitData.node4431 := by
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

def B4430 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4431, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq4430 : B4430.tree = HexagonCover.NBand.M8300_8500.SplitData.node4430 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4431
  · rfl
  · rfl
  · rfl

def B4429 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4430]
theorem treeEq4429 : B4429.tree = HexagonCover.NBand.M8300_8500.SplitData.node4429 := by
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
  · exact treeEq4430

def B4428 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4429, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4428 : B4428.tree = HexagonCover.NBand.M8300_8500.SplitData.node4428 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4429
  · rfl

def B4377 : Block := .branch 100 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4378, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B4428]
theorem treeEq4377 : B4377.tree = HexagonCover.NBand.M8300_8500.SplitData.node4377 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4428

theorem accepted4377 : B4377.accepted = true := by decide +kernel
theorem checked4377 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4377 (maskNeeds ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4377]
  exact B4377.sound accepted4377
#print axioms checked4377

end HexagonCover.NBand.M8300_8500.SplitTree.Run0060
