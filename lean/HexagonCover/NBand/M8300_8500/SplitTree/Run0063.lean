import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0060
import HexagonCover.NBand.M8300_8500.SplitTree.Run0061
import HexagonCover.NBand.M8300_8500.SplitTree.Run0062
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0063
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4369_4372 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4372 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0061.checked4372
def Tip4369_4454 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4454 ![2251799813685633, 360358888689632770, 37815861379901599782916, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0061.checked4454
def Tip4369_4466 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4466 ![2251799813685633, 377789678988460306728450, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0061.checked4466
def B4453 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq4453 : B4453.tree = HexagonCover.NBand.M8300_8500.SplitData.node4453 := by
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

def B4452 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B4453, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4452 : B4452.tree = HexagonCover.NBand.M8300_8500.SplitData.node4452 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4453
  · rfl
  · rfl

def B4451 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B4452, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4451 : B4451.tree = HexagonCover.NBand.M8300_8500.SplitData.node4451 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4452
  · rfl
  · rfl

def B4450 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B4451, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4450 : B4450.tree = HexagonCover.NBand.M8300_8500.SplitData.node4450 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4451
  · rfl
  · rfl

def B4449 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4450, (.leaf 0 [] 0)]
theorem treeEq4449 : B4449.tree = HexagonCover.NBand.M8300_8500.SplitData.node4449 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4450
  · rfl

def B4448 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4449, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4448 : B4448.tree = HexagonCover.NBand.M8300_8500.SplitData.node4448 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4449
  · rfl

def B4447 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B4448, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4447 : B4447.tree = HexagonCover.NBand.M8300_8500.SplitData.node4447 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4448
  · rfl
  · rfl

def B4446 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4447, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4446 : B4446.tree = HexagonCover.NBand.M8300_8500.SplitData.node4446 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4447
  · rfl
  · rfl
  · rfl

def B4445 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4446]
theorem treeEq4445 : B4445.tree = HexagonCover.NBand.M8300_8500.SplitData.node4445 := by
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
  · exact treeEq4446

def B4371 : Block := .branch 83 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip4369_4372, B4445, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq4371 : B4371.tree = HexagonCover.NBand.M8300_8500.SplitData.node4371 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4445
  · rfl
  · rfl
  · rfl

def B4370 : Block := .branch 82 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B4371, Tip4369_4454, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq4370 : B4370.tree = HexagonCover.NBand.M8300_8500.SplitData.node4370 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4371
  · rfl
  · rfl
  · rfl
  · rfl

def B4369 : Block := .branch 78 ![2251799813685633, 75558368199991088907778, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B4370, Tip4369_4466, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4369 : B4369.tree = HexagonCover.NBand.M8300_8500.SplitData.node4369 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4370
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4369 : B4369.accepted = true := by decide +kernel
theorem checked4369 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4369 (maskNeeds ![2251799813685633, 75558368199991088907778, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4369]
  exact B4369.sound accepted4369
#print axioms checked4369

def Tip4368_4481 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4481 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0062.checked4481
def Tip4368_4563 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4563 ![2251799813685633, 360358888689632770, 37815861379901599782916, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0062.checked4563
def Tip4368_4575 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4575 ![2251799813685633, 453347542714374630147586, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0062.checked4575
def Tip4368_4369 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4369 ![2251799813685633, 75558368199991088907778, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked4369
def B4562 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq4562 : B4562.tree = HexagonCover.NBand.M8300_8500.SplitData.node4562 := by
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

def B4561 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B4562, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4561 : B4561.tree = HexagonCover.NBand.M8300_8500.SplitData.node4561 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4562
  · rfl
  · rfl

def B4560 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B4561, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq4560 : B4560.tree = HexagonCover.NBand.M8300_8500.SplitData.node4560 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4561
  · rfl
  · rfl

def B4559 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B4560, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4559 : B4559.tree = HexagonCover.NBand.M8300_8500.SplitData.node4559 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4560
  · rfl
  · rfl

def B4558 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4559, (.leaf 0 [] 0)]
theorem treeEq4558 : B4558.tree = HexagonCover.NBand.M8300_8500.SplitData.node4558 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4559
  · rfl

def B4557 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4558, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4557 : B4557.tree = HexagonCover.NBand.M8300_8500.SplitData.node4557 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4558
  · rfl

def B4556 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B4557, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4556 : B4556.tree = HexagonCover.NBand.M8300_8500.SplitData.node4556 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4557
  · rfl
  · rfl

def B4555 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4556, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq4555 : B4555.tree = HexagonCover.NBand.M8300_8500.SplitData.node4555 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4556
  · rfl
  · rfl
  · rfl

def B4554 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4555]
theorem treeEq4554 : B4554.tree = HexagonCover.NBand.M8300_8500.SplitData.node4554 := by
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
  · exact treeEq4555

def B4480 : Block := .branch 83 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip4368_4481, B4554, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq4480 : B4480.tree = HexagonCover.NBand.M8300_8500.SplitData.node4480 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4554
  · rfl
  · rfl
  · rfl

def B4479 : Block := .branch 82 ![2251799813685633, 504474076765488642, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B4480, Tip4368_4563, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq4479 : B4479.tree = HexagonCover.NBand.M8300_8500.SplitData.node4479 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4480
  · rfl
  · rfl
  · rfl
  · rfl

def B4478 : Block := .branch 78 ![2251799813685633, 151116231925905412326914, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B4479, Tip4368_4575, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq4478 : B4478.tree = HexagonCover.NBand.M8300_8500.SplitData.node4478 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4479
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4368 : Block := .branch 76 ![2251799813685633, 151116231925905412326914, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip4368_4369, B4478, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq4368 : B4368.tree = HexagonCover.NBand.M8300_8500.SplitData.node4368 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4478
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4368 : B4368.accepted = true := by decide +kernel
theorem checked4368 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4368 (maskNeeds ![2251799813685633, 151116231925905412326914, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4368]
  exact B4368.sound accepted4368
#print axioms checked4368

def Tip4123_4124 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4124 ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0060.checked4124
def B4366 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4366 : B4366.tree = HexagonCover.NBand.M8300_8500.SplitData.node4366 := by
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

def B4365 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4366, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4365 : B4365.tree = HexagonCover.NBand.M8300_8500.SplitData.node4365 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4366
  · rfl

def B4364 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4365, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4364 : B4364.tree = HexagonCover.NBand.M8300_8500.SplitData.node4364 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4365
  · rfl
  · rfl
  · rfl
  · rfl

def B4363 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4364, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4363 : B4363.tree = HexagonCover.NBand.M8300_8500.SplitData.node4363 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4364
  · rfl
  · rfl
  · rfl
  · rfl

def B4362 : Block := .branch 161 ![2251799813685633, 360358888689632770, 77409031423228021361874948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1002).pointIds 1002), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4363]
theorem treeEq4362 : B4362.tree = HexagonCover.NBand.M8300_8500.SplitData.node4362 := by
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
  · exact treeEq4363

def B4361 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4362, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4361 : B4361.tree = HexagonCover.NBand.M8300_8500.SplitData.node4361 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4362
  · rfl
  · rfl
  · rfl
  · rfl

def B4360 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4361, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4360 : B4360.tree = HexagonCover.NBand.M8300_8500.SplitData.node4360 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4361
  · rfl
  · rfl

def B4359 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4360, (.leaf 0 [] 0)]
theorem treeEq4359 : B4359.tree = HexagonCover.NBand.M8300_8500.SplitData.node4359 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4360
  · rfl

def B4358 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4359, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4358 : B4358.tree = HexagonCover.NBand.M8300_8500.SplitData.node4358 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4359
  · rfl

def B4357 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4358, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4357 : B4357.tree = HexagonCover.NBand.M8300_8500.SplitData.node4357 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4358
  · rfl
  · rfl

def B4356 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4357, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4356 : B4356.tree = HexagonCover.NBand.M8300_8500.SplitData.node4356 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4357
  · rfl
  · rfl
  · rfl

def B4355 : Block := .branch 160 ![2251799813685633, 151448129204044108400130, 37778967891754180679684, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 1001).pointIds 1001), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4356]
theorem treeEq4355 : B4355.tree = HexagonCover.NBand.M8300_8500.SplitData.node4355 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4356

def B4123 : Block := .branch 68 ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip4123_4124, B4355, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq4123 : B4123.tree = HexagonCover.NBand.M8300_8500.SplitData.node4123 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4123 : B4123.accepted = true := by decide +kernel
theorem checked4123 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4123 (maskNeeds ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4123]
  exact B4123.sound accepted4123
#print axioms checked4123

def Tip4122_4368 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4368 ![2251799813685633, 151116231925905412326914, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked4368
def Tip4122_4123 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4123 ![2251799813685633, 151153125414052831430146, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked4123
def B4598 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4598 : B4598.tree = HexagonCover.NBand.M8300_8500.SplitData.node4598 := by
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

def B4597 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4598, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4597 : B4597.tree = HexagonCover.NBand.M8300_8500.SplitData.node4597 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4598
  · rfl

def B4596 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4597, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4596 : B4596.tree = HexagonCover.NBand.M8300_8500.SplitData.node4596 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4597
  · rfl
  · rfl
  · rfl
  · rfl

def B4595 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4596, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4595 : B4595.tree = HexagonCover.NBand.M8300_8500.SplitData.node4595 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4596
  · rfl
  · rfl
  · rfl
  · rfl

def B4594 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4595, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4594 : B4594.tree = HexagonCover.NBand.M8300_8500.SplitData.node4594 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4595
  · rfl
  · rfl
  · rfl
  · rfl

def B4593 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4594, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4593 : B4593.tree = HexagonCover.NBand.M8300_8500.SplitData.node4593 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4594
  · rfl
  · rfl

def B4592 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4593, (.leaf 0 [] 0)]
theorem treeEq4592 : B4592.tree = HexagonCover.NBand.M8300_8500.SplitData.node4592 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4593
  · rfl

def B4591 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4592, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4591 : B4591.tree = HexagonCover.NBand.M8300_8500.SplitData.node4591 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4592
  · rfl

def B4590 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4591, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4590 : B4590.tree = HexagonCover.NBand.M8300_8500.SplitData.node4590 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4591
  · rfl
  · rfl

def B4589 : Block := .branch 161 ![2251799813685633, 360358888689632770, 37815861379901599782916, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1004).pointIds 1004), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4590]
theorem treeEq4589 : B4589.tree = HexagonCover.NBand.M8300_8500.SplitData.node4589 := by
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
  · exact treeEq4590

def B4588 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4589, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4588 : B4588.tree = HexagonCover.NBand.M8300_8500.SplitData.node4588 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4589
  · rfl
  · rfl
  · rfl

def B4587 : Block := .branch 160 ![2251799813685633, 151411235715896689296898, 37815861379901599782916, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1006).pointIds 1006), (.leaf 2 (Common.fact 1001).pointIds 1001), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4588]
theorem treeEq4587 : B4587.tree = HexagonCover.NBand.M8300_8500.SplitData.node4587 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4588

def B4367 : Block := .branch 68 ![2251799813685633, 151116231925905412326914, 37815861379901599782916, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip4122_4368, B4587, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq4367 : B4367.tree = HexagonCover.NBand.M8300_8500.SplitData.node4367 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4587
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4122 : Block := .branch 65 ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 143).pointIds 143), Tip4122_4123, B4367, (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 147).pointIds 147)]
theorem treeEq4122 : B4122.tree = HexagonCover.NBand.M8300_8500.SplitData.node4122 := by
  change Tree.branch (65 : Fin 177) _ = Tree.branch (65 : Fin 177) _
  apply congrArg (Tree.branch (65 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4367
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4122 : B4122.accepted = true := by decide +kernel
theorem checked4122 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4122 (maskNeeds ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq4122]
  exact B4122.sound accepted4122
#print axioms checked4122

def Tip4114_4122 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4122 ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked4122
def B4610 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4610 : B4610.tree = HexagonCover.NBand.M8300_8500.SplitData.node4610 := by
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

def B4609 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4610, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4609 : B4609.tree = HexagonCover.NBand.M8300_8500.SplitData.node4609 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4610
  · rfl

def B4608 : Block := .branch 84 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4609, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4608 : B4608.tree = HexagonCover.NBand.M8300_8500.SplitData.node4608 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4609
  · rfl
  · rfl
  · rfl
  · rfl

def B4607 : Block := .branch 85 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4608, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4607 : B4607.tree = HexagonCover.NBand.M8300_8500.SplitData.node4607 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4608
  · rfl
  · rfl
  · rfl
  · rfl

def B4606 : Block := .branch 161 ![2251799813685633, 360358888689632770, 77409031423228021361874948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1002).pointIds 1002), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4607]
theorem treeEq4606 : B4606.tree = HexagonCover.NBand.M8300_8500.SplitData.node4606 := by
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
  · exact treeEq4607

def B4605 : Block := .branch 86 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4606, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4605 : B4605.tree = HexagonCover.NBand.M8300_8500.SplitData.node4605 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4606
  · rfl
  · rfl
  · rfl
  · rfl

def B4604 : Block := .branch 138 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4605, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4604 : B4604.tree = HexagonCover.NBand.M8300_8500.SplitData.node4604 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4605
  · rfl
  · rfl

def B4603 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4604, (.leaf 0 [] 0)]
theorem treeEq4603 : B4603.tree = HexagonCover.NBand.M8300_8500.SplitData.node4603 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4604
  · rfl

def B4602 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4603, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4602 : B4602.tree = HexagonCover.NBand.M8300_8500.SplitData.node4602 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4603
  · rfl

def B4601 : Block := .branch 146 ![2251799813685633, 360358888689632770, 37778967891754180679684, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4602, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4601 : B4601.tree = HexagonCover.NBand.M8300_8500.SplitData.node4601 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4602
  · rfl
  · rfl

def B4600 : Block := .branch 170 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4601, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4600 : B4600.tree = HexagonCover.NBand.M8300_8500.SplitData.node4600 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4601
  · rfl
  · rfl
  · rfl

def B4599 : Block := .branch 160 ![2251799813685633, 151116664271469639894530, 37778967891754180679684, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1007).pointIds 1007), (.leaf 2 (Common.fact 1001).pointIds 1001), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4600]
theorem treeEq4599 : B4599.tree = HexagonCover.NBand.M8300_8500.SplitData.node4599 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4600

def B4121 : Block := .branch 59 ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip4114_4122, B4599, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq4121 : B4121.tree = HexagonCover.NBand.M8300_8500.SplitData.node4121 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4599
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4120 : Block := .branch 109 ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B4121, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq4120 : B4120.tree = HexagonCover.NBand.M8300_8500.SplitData.node4120 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4121
  · rfl
  · rfl

def B4119 : Block := .branch 171 ![2251799813685633, 151116231925905412326914, 37778967891754180679684, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 981).pointIds 981), (.leaf 1 (Common.fact 992).pointIds 992), (.leaf 2 (Common.fact 993).pointIds 993), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B4120]
theorem treeEq4119 : B4119.tree = HexagonCover.NBand.M8300_8500.SplitData.node4119 := by
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
  · exact treeEq4120

def B4118 : Block := .branch 77 ![2251799813685633, 504474076765488642, 37778967891754180679684, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 163).pointIds 163), B4119, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq4118 : B4118.tree = HexagonCover.NBand.M8300_8500.SplitData.node4118 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4119
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4117 : Block := .branch 79 ![2251799813685633, 504474076765488642, 37778967891754180679684, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B4118, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq4117 : B4117.tree = HexagonCover.NBand.M8300_8500.SplitData.node4117 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4118
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4116 : Block := .branch 97 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B4117, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq4116 : B4116.tree = HexagonCover.NBand.M8300_8500.SplitData.node4116 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4117
  · rfl
  · rfl
  · rfl

def B4115 : Block := .branch 80 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B4116, (.leaf 1 (Common.fact 947).pointIds 947), (.leaf 2 (Common.fact 948).pointIds 948), (.leaf 3 (Common.fact 949).pointIds 949), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 951).pointIds 951), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq4115 : B4115.tree = HexagonCover.NBand.M8300_8500.SplitData.node4115 := by
  change Tree.branch (80 : Fin 177) _ = Tree.branch (80 : Fin 177) _
  apply congrArg (Tree.branch (80 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4116
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4114 : Block := .branch 107 ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B4115, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq4114 : B4114.tree = HexagonCover.NBand.M8300_8500.SplitData.node4114 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4115
  · rfl
  · rfl
  · rfl

theorem accepted4114 : B4114.accepted = true := by decide +kernel
theorem checked4114 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4114 (maskNeeds ![2251799813685633, 504474076765488642, 37778967891754180679684, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq4114]
  exact B4114.sound accepted4114
#print axioms checked4114

end HexagonCover.NBand.M8300_8500.SplitTree.Run0063
