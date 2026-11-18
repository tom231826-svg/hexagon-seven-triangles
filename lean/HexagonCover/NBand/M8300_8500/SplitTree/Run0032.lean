import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0029
import HexagonCover.NBand.M8300_8500.SplitTree.Run0030
import HexagonCover.NBand.M8300_8500.SplitTree.Run0031
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0032
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip2141_2144 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2144 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0030.checked2144
def Tip2141_2226 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2226 ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0030.checked2226
def Tip2141_2238 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2238 ![578712552117109121, 377789714946888581514754, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0030.checked2238
def B2225 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq2225 : B2225.tree = HexagonCover.NBand.M8300_8500.SplitData.node2225 := by
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

def B2224 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B2225, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2224 : B2224.tree = HexagonCover.NBand.M8300_8500.SplitData.node2224 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2225
  · rfl
  · rfl

def B2223 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B2224, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2223 : B2223.tree = HexagonCover.NBand.M8300_8500.SplitData.node2223 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2224
  · rfl
  · rfl

def B2222 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B2223, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2222 : B2222.tree = HexagonCover.NBand.M8300_8500.SplitData.node2222 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2223
  · rfl
  · rfl

def B2221 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2222, (.leaf 0 [] 0)]
theorem treeEq2221 : B2221.tree = HexagonCover.NBand.M8300_8500.SplitData.node2221 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2222
  · rfl

def B2220 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2221, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2220 : B2220.tree = HexagonCover.NBand.M8300_8500.SplitData.node2220 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2221
  · rfl

def B2219 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B2220, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2219 : B2219.tree = HexagonCover.NBand.M8300_8500.SplitData.node2219 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2220
  · rfl
  · rfl

def B2218 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2219, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2218 : B2218.tree = HexagonCover.NBand.M8300_8500.SplitData.node2218 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2219
  · rfl
  · rfl
  · rfl

def B2217 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2218]
theorem treeEq2217 : B2217.tree = HexagonCover.NBand.M8300_8500.SplitData.node2217 := by
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
  · exact treeEq2218

def B2143 : Block := .branch 83 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip2141_2144, B2217, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq2143 : B2143.tree = HexagonCover.NBand.M8300_8500.SplitData.node2143 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2217
  · rfl
  · rfl
  · rfl

def B2142 : Block := .branch 82 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B2143, Tip2141_2226, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq2142 : B2142.tree = HexagonCover.NBand.M8300_8500.SplitData.node2142 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2143
  · rfl
  · rfl
  · rfl
  · rfl

def B2141 : Block := .branch 78 ![578712552117109121, 75558404158419363694082, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B2142, Tip2141_2238, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2141 : B2141.tree = HexagonCover.NBand.M8300_8500.SplitData.node2141 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2142
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2141 : B2141.accepted = true := by decide +kernel
theorem checked2141 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2141 (maskNeeds ![578712552117109121, 75558404158419363694082, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2141]
  exact B2141.sound accepted2141
#print axioms checked2141

def Tip2140_2253 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2253 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0031.checked2253
def Tip2140_2335 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2335 ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0031.checked2335
def Tip2140_2347 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2347 ![578712552117109121, 453347578672802904933890, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] HexagonCover.NBand.M8300_8500.SplitTree.Run0031.checked2347
def Tip2140_2141 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2141 ![578712552117109121, 75558404158419363694082, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked2141
def B2334 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq2334 : B2334.tree = HexagonCover.NBand.M8300_8500.SplitData.node2334 := by
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

def B2333 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B2334, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2333 : B2333.tree = HexagonCover.NBand.M8300_8500.SplitData.node2333 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2334
  · rfl
  · rfl

def B2332 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B2333, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2332 : B2332.tree = HexagonCover.NBand.M8300_8500.SplitData.node2332 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2333
  · rfl
  · rfl

def B2331 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B2332, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2331 : B2331.tree = HexagonCover.NBand.M8300_8500.SplitData.node2331 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2332
  · rfl
  · rfl

def B2330 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2331, (.leaf 0 [] 0)]
theorem treeEq2330 : B2330.tree = HexagonCover.NBand.M8300_8500.SplitData.node2330 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2331
  · rfl

def B2329 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2330, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2329 : B2329.tree = HexagonCover.NBand.M8300_8500.SplitData.node2329 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2330
  · rfl

def B2328 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B2329, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2328 : B2328.tree = HexagonCover.NBand.M8300_8500.SplitData.node2328 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2329
  · rfl
  · rfl

def B2327 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2328, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2327 : B2327.tree = HexagonCover.NBand.M8300_8500.SplitData.node2327 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2328
  · rfl
  · rfl
  · rfl

def B2326 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158465996435085592220485574664, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 972).pointIds 972), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2327]
theorem treeEq2326 : B2326.tree = HexagonCover.NBand.M8300_8500.SplitData.node2326 := by
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
  · exact treeEq2327

def B2252 : Block := .branch 83 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip2140_2253, B2326, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq2252 : B2252.tree = HexagonCover.NBand.M8300_8500.SplitData.node2252 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2326
  · rfl
  · rfl
  · rfl

def B2251 : Block := .branch 82 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B2252, Tip2140_2335, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq2251 : B2251.tree = HexagonCover.NBand.M8300_8500.SplitData.node2251 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2252
  · rfl
  · rfl
  · rfl
  · rfl

def B2250 : Block := .branch 78 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B2251, Tip2140_2347, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2250 : B2250.tree = HexagonCover.NBand.M8300_8500.SplitData.node2250 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2251
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2140 : Block := .branch 76 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip2140_2141, B2250, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2140 : B2140.tree = HexagonCover.NBand.M8300_8500.SplitData.node2140 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2250
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2140 : B2140.accepted = true := by decide +kernel
theorem checked2140 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2140 (maskNeeds ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2140]
  exact B2140.sound accepted2140
#print axioms checked2140

def Tip2132_2140 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2140 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked2140
def B2370 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq2370 : B2370.tree = HexagonCover.NBand.M8300_8500.SplitData.node2370 := by
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

def B2369 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2370, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq2369 : B2369.tree = HexagonCover.NBand.M8300_8500.SplitData.node2369 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2370
  · rfl

def B2368 : Block := .branch 84 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2369, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2368 : B2368.tree = HexagonCover.NBand.M8300_8500.SplitData.node2368 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2369
  · rfl
  · rfl
  · rfl
  · rfl

def B2367 : Block := .branch 85 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2368, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2367 : B2367.tree = HexagonCover.NBand.M8300_8500.SplitData.node2367 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2368
  · rfl
  · rfl
  · rfl
  · rfl

def B2366 : Block := .branch 86 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2367, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2366 : B2366.tree = HexagonCover.NBand.M8300_8500.SplitData.node2366 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2367
  · rfl
  · rfl
  · rfl
  · rfl

def B2365 : Block := .branch 138 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B2366, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2365 : B2365.tree = HexagonCover.NBand.M8300_8500.SplitData.node2365 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2366
  · rfl
  · rfl

def B2364 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2365, (.leaf 0 [] 0)]
theorem treeEq2364 : B2364.tree = HexagonCover.NBand.M8300_8500.SplitData.node2364 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2365
  · rfl

def B2363 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2364, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2363 : B2363.tree = HexagonCover.NBand.M8300_8500.SplitData.node2363 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2364
  · rfl

def B2362 : Block := .branch 146 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B2363, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2362 : B2362.tree = HexagonCover.NBand.M8300_8500.SplitData.node2362 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2363
  · rfl
  · rfl

def B2361 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2362]
theorem treeEq2361 : B2361.tree = HexagonCover.NBand.M8300_8500.SplitData.node2361 := by
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
  · exact treeEq2362

def B2360 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2361, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq2360 : B2360.tree = HexagonCover.NBand.M8300_8500.SplitData.node2360 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2361
  · rfl
  · rfl
  · rfl

def B2359 : Block := .branch 160 ![578712552117109121, 151411271674324964083202, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 978).pointIds 978), (.leaf 2 (Common.fact 975).pointIds 975), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B2360]
theorem treeEq2359 : B2359.tree = HexagonCover.NBand.M8300_8500.SplitData.node2359 := by
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
  · exact treeEq2360

def B2139 : Block := .branch 68 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip2132_2140, B2359, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq2139 : B2139.tree = HexagonCover.NBand.M8300_8500.SplitData.node2139 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2359
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2138 : Block := .branch 109 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2139, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq2138 : B2138.tree = HexagonCover.NBand.M8300_8500.SplitData.node2138 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2139
  · rfl
  · rfl

def B2137 : Block := .branch 171 ![578712552117109121, 151116267884333687113218, 37815825351104580818948, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 955).pointIds 955), (.leaf 1 (Common.fact 956).pointIds 956), (.leaf 2 (Common.fact 957).pointIds 957), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B2138]
theorem treeEq2137 : B2137.tree = HexagonCover.NBand.M8300_8500.SplitData.node2137 := by
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
  · exact treeEq2138

def B2136 : Block := .branch 77 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 163).pointIds 163), B2137, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2136 : B2136.tree = HexagonCover.NBand.M8300_8500.SplitData.node2136 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2137
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2135 : Block := .branch 79 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B2136, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2135 : B2135.tree = HexagonCover.NBand.M8300_8500.SplitData.node2135 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2136
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2134 : Block := .branch 97 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B2135, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq2134 : B2134.tree = HexagonCover.NBand.M8300_8500.SplitData.node2134 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2135
  · rfl
  · rfl
  · rfl

def B2133 : Block := .branch 80 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B2134, (.leaf 1 (Common.fact 947).pointIds 947), (.leaf 2 (Common.fact 948).pointIds 948), (.leaf 3 (Common.fact 949).pointIds 949), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 951).pointIds 951), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2133 : B2133.tree = HexagonCover.NBand.M8300_8500.SplitData.node2133 := by
  change Tree.branch (80 : Fin 177) _ = Tree.branch (80 : Fin 177) _
  apply congrArg (Tree.branch (80 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2134
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2132 : Block := .branch 107 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2133, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2132 : B2132.tree = HexagonCover.NBand.M8300_8500.SplitData.node2132 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2133
  · rfl
  · rfl
  · rfl

theorem accepted2132 : B2132.accepted = true := by decide +kernel
theorem checked2132 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2132 (maskNeeds ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq2132]
  exact B2132.sound accepted2132
#print axioms checked2132

def Tip0026_0028 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0028 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0029.checked0028
def B2117 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 11150372599265311570767859136324180753088528, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 937).pointIds 937), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq2117 : B2117.tree = HexagonCover.NBand.M8300_8500.SplitData.node2117 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2116 : Block := .branch 143 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B2117, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2116 : B2116.tree = HexagonCover.NBand.M8300_8500.SplitData.node2116 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2117
  · rfl
  · rfl

def B2115 : Block := .branch 144 ![385, 1538, 6148, 81169252495863813864585777143816, 98320, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B2116, (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq2115 : B2115.tree = HexagonCover.NBand.M8300_8500.SplitData.node2115 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2116
  · rfl

def B2114 : Block := .branch 107 ![385, 1538, 6148, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2115, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2114 : B2114.tree = HexagonCover.NBand.M8300_8500.SplitData.node2114 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2115
  · rfl
  · rfl
  · rfl

def B2113 : Block := .branch 118 ![385, 1538, 6148, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B2114, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2113 : B2113.tree = HexagonCover.NBand.M8300_8500.SplitData.node2113 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2114
  · rfl
  · rfl
  · rfl

def B2112 : Block := .branch 128 ![385, 1538, 6148, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2113, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2112 : B2112.tree = HexagonCover.NBand.M8300_8500.SplitData.node2112 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2113
  · rfl
  · rfl
  · rfl

def B2111 : Block := .branch 151 ![385, 1538, 6148, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979261624969978204127296] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2112, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 934).pointIds 934)]
theorem treeEq2111 : B2111.tree = HexagonCover.NBand.M8300_8500.SplitData.node2111 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2112
  · rfl
  · rfl

def B0027 : Block := .branch 67 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 153).pointIds 153), Tip0026_0028, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B2111]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M8300_8500.SplitData.node0027 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2111

def B2124 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 11150372599265311570767859136324180753088528, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq2124 : B2124.tree = HexagonCover.NBand.M8300_8500.SplitData.node2124 := by
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

def B2123 : Block := .branch 143 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B2124, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq2123 : B2123.tree = HexagonCover.NBand.M8300_8500.SplitData.node2123 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2124
  · rfl
  · rfl

def B2122 : Block := .branch 144 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B2123, (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2122 : B2122.tree = HexagonCover.NBand.M8300_8500.SplitData.node2122 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2123
  · rfl

def B2121 : Block := .branch 107 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2122, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2121 : B2121.tree = HexagonCover.NBand.M8300_8500.SplitData.node2121 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2122
  · rfl
  · rfl
  · rfl

def B2120 : Block := .branch 118 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B2121, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2120 : B2120.tree = HexagonCover.NBand.M8300_8500.SplitData.node2120 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2121
  · rfl
  · rfl
  · rfl

def B2119 : Block := .branch 128 ![385, 1538, 6148, 81129638414606681695789005168648, 3032901347000164747248857685080177164813434896, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2120, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2119 : B2119.tree = HexagonCover.NBand.M8300_8500.SplitData.node2119 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2120
  · rfl
  · rfl
  · rfl

def B2118 : Block := .branch 151 ![385, 1538, 6148, 81129638414606681695789005168648, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979187837993683365920832] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2119, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq2118 : B2118.tree = HexagonCover.NBand.M8300_8500.SplitData.node2118 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2119
  · rfl
  · rfl

def B0026 : Block := .branch 66 ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 148).pointIds 148), B0027, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B2118]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M8300_8500.SplitData.node0026 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0027
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2118

theorem accepted0026 : B0026.accepted = true := by decide +kernel
theorem checked0026 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0026 (maskNeeds ![578712552117109121, 37037603885250774530, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0026]
  exact B0026.sound accepted0026
#print axioms checked0026

def B2423 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2423 : B2423.tree = HexagonCover.NBand.M8300_8500.SplitData.node2423 := by
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

def B2422 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2423, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq2422 : B2422.tree = HexagonCover.NBand.M8300_8500.SplitData.node2422 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2423
  · rfl
  · rfl

def B2421 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B2422, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq2421 : B2421.tree = HexagonCover.NBand.M8300_8500.SplitData.node2421 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2422
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2420 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B2421, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq2420 : B2420.tree = HexagonCover.NBand.M8300_8500.SplitData.node2420 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2421
  · rfl
  · rfl
  · rfl
  · rfl

def B2419 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B2420]
theorem treeEq2419 : B2419.tree = HexagonCover.NBand.M8300_8500.SplitData.node2419 := by
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
  · exact treeEq2420

def B2418 : Block := .branch 169 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2419, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq2418 : B2418.tree = HexagonCover.NBand.M8300_8500.SplitData.node2418 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2419
  · rfl

def B2417 : Block := .branch 138 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944466912589573234605283144949207269408, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B2418, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2417 : B2417.tree = HexagonCover.NBand.M8300_8500.SplitData.node2417 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2418
  · rfl
  · rfl

def B2416 : Block := .branch 165 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355573530071658587684226515959365894176, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B2417, (.leaf 0 [] 0)]
theorem treeEq2416 : B2416.tree = HexagonCover.NBand.M8300_8500.SplitData.node2416 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2417
  · rfl

def B2415 : Block := .branch 167 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B2416, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2415 : B2415.tree = HexagonCover.NBand.M8300_8500.SplitData.node2415 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2416
  · rfl

def B2414 : Block := .branch 146 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B2415, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2414 : B2414.tree = HexagonCover.NBand.M8300_8500.SplitData.node2414 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2415
  · rfl
  · rfl

def B2413 : Block := .branch 170 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582620114145322302633222186454766830747712] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B2414, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2413 : B2413.tree = HexagonCover.NBand.M8300_8500.SplitData.node2413 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2414
  · rfl
  · rfl
  · rfl

theorem accepted2413 : B2413.accepted = true := by decide +kernel
theorem checked2413 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2413 (maskNeeds ![2251799813685633, 972778069267842562, 4873482210321473860540420, 664614077120620450716241123684147208, 179799760822258177755780327834407847243907088, 393248, 3367299783582620114145322302633222186454766830747712]) := by
  rw [← treeEq2413]
  exact B2413.sound accepted2413
#print axioms checked2413

end HexagonCover.NBand.M8300_8500.SplitTree.Run0032
