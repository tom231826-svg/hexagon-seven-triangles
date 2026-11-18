import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0029
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0030
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip2144_2149 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2149 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0029.checked2149
def B2208 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2208 : B2208.tree = HexagonCover.NBand.M8300_8500.SplitData.node2208 := by
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

def B2207 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2208, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2207 : B2207.tree = HexagonCover.NBand.M8300_8500.SplitData.node2207 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2208
  · rfl

def B2206 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B2207]
theorem treeEq2206 : B2206.tree = HexagonCover.NBand.M8300_8500.SplitData.node2206 := by
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
  · exact treeEq2207

def B2205 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B2206, (.leaf 0 [] 0)]
theorem treeEq2205 : B2205.tree = HexagonCover.NBand.M8300_8500.SplitData.node2205 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2206
  · rfl

def B2204 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B2205, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2204 : B2204.tree = HexagonCover.NBand.M8300_8500.SplitData.node2204 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2205
  · rfl

def B2148 : Block := .branch 98 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip2144_2149, B2204, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq2148 : B2148.tree = HexagonCover.NBand.M8300_8500.SplitData.node2148 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2204
  · rfl
  · rfl

def B2210 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq2210 : B2210.tree = HexagonCover.NBand.M8300_8500.SplitData.node2210 := by
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

def B2209 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 24584, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2210, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq2209 : B2209.tree = HexagonCover.NBand.M8300_8500.SplitData.node2209 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2210
  · rfl
  · rfl
  · rfl

def B2147 : Block := .branch 90 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B2148, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B2209]
theorem treeEq2147 : B2147.tree = HexagonCover.NBand.M8300_8500.SplitData.node2147 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2148
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2209

def B2212 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 77371252455336267181219848, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 687).pointIds 687), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2212 : B2212.tree = HexagonCover.NBand.M8300_8500.SplitData.node2212 := by
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

def B2211 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 77371252455336267181219848, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2212]
theorem treeEq2211 : B2211.tree = HexagonCover.NBand.M8300_8500.SplitData.node2211 := by
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
  · exact treeEq2212

def B2146 : Block := .branch 86 ![578712552117109121, 540432505040274946, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2147, B2211, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2146 : B2146.tree = HexagonCover.NBand.M8300_8500.SplitData.node2146 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2147
  · exact treeEq2211
  · rfl
  · rfl
  · rfl

def B2214 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 158495010654756343320678522888, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 969).pointIds 969), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2214 : B2214.tree = HexagonCover.NBand.M8300_8500.SplitData.node2214 := by
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

def B2213 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158495010654756343320678522888, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2214]
theorem treeEq2213 : B2213.tree = HexagonCover.NBand.M8300_8500.SplitData.node2213 := by
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
  · exact treeEq2214

def B2145 : Block := .branch 85 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2146, B2213, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2145 : B2145.tree = HexagonCover.NBand.M8300_8500.SplitData.node2145 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2146
  · exact treeEq2213
  · rfl
  · rfl
  · rfl

def B2216 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 158475667841642509253883224072, 98320, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 971).pointIds 971), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2216 : B2216.tree = HexagonCover.NBand.M8300_8500.SplitData.node2216 := by
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

def B2215 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 158475667841642509253883224072, 178405961588244985132285746181186892047941648, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), (.leaf 3 (Common.fact 970).pointIds 970), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2216]
theorem treeEq2215 : B2215.tree = HexagonCover.NBand.M8300_8500.SplitData.node2215 := by
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
  · exact treeEq2216

def B2144 : Block := .branch 84 ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2145, B2215, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2144 : B2144.tree = HexagonCover.NBand.M8300_8500.SplitData.node2144 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2145
  · exact treeEq2215
  · rfl
  · rfl
  · rfl

theorem accepted2144 : B2144.accepted = true := by decide +kernel
theorem checked2144 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2144 (maskNeeds ![578712552117109121, 540432505040274946, 37815825351104580818948, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2144]
  exact B2144.sound accepted2144
#print axioms checked2144

def B2237 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq2237 : B2237.tree = HexagonCover.NBand.M8300_8500.SplitData.node2237 := by
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
  · rfl

def B2236 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2237, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2236 : B2236.tree = HexagonCover.NBand.M8300_8500.SplitData.node2236 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2237
  · rfl

def B2235 : Block := .branch 84 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2236, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2235 : B2235.tree = HexagonCover.NBand.M8300_8500.SplitData.node2235 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2236
  · rfl
  · rfl
  · rfl
  · rfl

def B2234 : Block := .branch 85 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2235, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2234 : B2234.tree = HexagonCover.NBand.M8300_8500.SplitData.node2234 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2235
  · rfl
  · rfl
  · rfl
  · rfl

def B2233 : Block := .branch 86 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2234, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2233 : B2233.tree = HexagonCover.NBand.M8300_8500.SplitData.node2233 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2234
  · rfl
  · rfl
  · rfl
  · rfl

def B2232 : Block := .branch 129 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B2233, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2232 : B2232.tree = HexagonCover.NBand.M8300_8500.SplitData.node2232 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2233
  · rfl
  · rfl

def B2231 : Block := .branch 138 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B2232, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2231 : B2231.tree = HexagonCover.NBand.M8300_8500.SplitData.node2231 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2232
  · rfl
  · rfl

def B2230 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2231, (.leaf 0 [] 0)]
theorem treeEq2230 : B2230.tree = HexagonCover.NBand.M8300_8500.SplitData.node2230 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2231
  · rfl

def B2229 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2230, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2229 : B2229.tree = HexagonCover.NBand.M8300_8500.SplitData.node2229 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2230
  · rfl

def B2228 : Block := .branch 146 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B2229, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2228 : B2228.tree = HexagonCover.NBand.M8300_8500.SplitData.node2228 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2229
  · rfl
  · rfl

def B2227 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2228, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2227 : B2227.tree = HexagonCover.NBand.M8300_8500.SplitData.node2227 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2228
  · rfl
  · rfl
  · rfl

def B2226 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 973).pointIds 973), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2227]
theorem treeEq2226 : B2226.tree = HexagonCover.NBand.M8300_8500.SplitData.node2226 := by
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
  · exact treeEq2227

theorem accepted2226 : B2226.accepted = true := by decide +kernel
theorem checked2226 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2226 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq2226]
  exact B2226.sound accepted2226
#print axioms checked2226

def B2249 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq2249 : B2249.tree = HexagonCover.NBand.M8300_8500.SplitData.node2249 := by
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

def B2248 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2249, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq2248 : B2248.tree = HexagonCover.NBand.M8300_8500.SplitData.node2248 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2249
  · rfl

def B2247 : Block := .branch 84 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2248, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2247 : B2247.tree = HexagonCover.NBand.M8300_8500.SplitData.node2247 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2248
  · rfl
  · rfl
  · rfl
  · rfl

def B2246 : Block := .branch 85 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2247, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2246 : B2246.tree = HexagonCover.NBand.M8300_8500.SplitData.node2246 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2247
  · rfl
  · rfl
  · rfl
  · rfl

def B2245 : Block := .branch 86 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2246, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2245 : B2245.tree = HexagonCover.NBand.M8300_8500.SplitData.node2245 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2246
  · rfl
  · rfl
  · rfl
  · rfl

def B2244 : Block := .branch 138 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B2245, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2244 : B2244.tree = HexagonCover.NBand.M8300_8500.SplitData.node2244 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2245
  · rfl
  · rfl

def B2243 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2244, (.leaf 0 [] 0)]
theorem treeEq2243 : B2243.tree = HexagonCover.NBand.M8300_8500.SplitData.node2243 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2244
  · rfl

def B2242 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2243, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2242 : B2242.tree = HexagonCover.NBand.M8300_8500.SplitData.node2242 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2243
  · rfl

def B2241 : Block := .branch 146 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B2242, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2241 : B2241.tree = HexagonCover.NBand.M8300_8500.SplitData.node2241 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2242
  · rfl
  · rfl

def B2240 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2241]
theorem treeEq2240 : B2240.tree = HexagonCover.NBand.M8300_8500.SplitData.node2240 := by
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
  · exact treeEq2241

def B2239 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2240, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq2239 : B2239.tree = HexagonCover.NBand.M8300_8500.SplitData.node2239 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2240
  · rfl
  · rfl
  · rfl

def B2238 : Block := .branch 160 ![578712552117109121, 377789714946888581514754, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 974).pointIds 974), (.leaf 2 (Common.fact 975).pointIds 975), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B2239]
theorem treeEq2238 : B2238.tree = HexagonCover.NBand.M8300_8500.SplitData.node2238 := by
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
  · exact treeEq2239

theorem accepted2238 : B2238.accepted = true := by decide +kernel
theorem checked2238 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2238 (maskNeeds ![578712552117109121, 377789714946888581514754, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq2238]
  exact B2238.sound accepted2238
#print axioms checked2238

def B2267 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq2267 : B2267.tree = HexagonCover.NBand.M8300_8500.SplitData.node2267 := by
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

def B2266 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2267, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq2266 : B2266.tree = HexagonCover.NBand.M8300_8500.SplitData.node2266 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2267
  · rfl
  · rfl
  · rfl

def B2265 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42535295865117307932921825928971419680, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B2266]
theorem treeEq2265 : B2265.tree = HexagonCover.NBand.M8300_8500.SplitData.node2265 := by
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
  · exact treeEq2266

def B2271 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556142965880123323311949751266331459616, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq2271 : B2271.tree = HexagonCover.NBand.M8300_8500.SplitData.node2271 := by
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

def B2270 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2271, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq2270 : B2270.tree = HexagonCover.NBand.M8300_8500.SplitData.node2270 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2271
  · rfl

def B2269 : Block := .branch 161 ![578712552117109121, 396317316964419074, 37815825351104580818948, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2270]
theorem treeEq2269 : B2269.tree = HexagonCover.NBand.M8300_8500.SplitData.node2269 := by
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
  · exact treeEq2270

def B2268 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2269, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2268 : B2268.tree = HexagonCover.NBand.M8300_8500.SplitData.node2268 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2269
  · rfl
  · rfl
  · rfl

def B2264 : Block := .branch 125 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B2265, B2268]
theorem treeEq2264 : B2264.tree = HexagonCover.NBand.M8300_8500.SplitData.node2264 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2265
  · exact treeEq2268

def B2275 : Block := .branch 161 ![385, 1538, 37815825351104580818948, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2275 : B2275.tree = HexagonCover.NBand.M8300_8500.SplitData.node2275 := by
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

def B2274 : Block := .branch 170 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 963).pointIds 963), (.leaf 1 (Common.fact 964).pointIds 964), (.leaf 2 (Common.fact 965).pointIds 965), B2275, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2274 : B2274.tree = HexagonCover.NBand.M8300_8500.SplitData.node2274 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2275
  · rfl
  · rfl
  · rfl

def B2273 : Block := .branch 135 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422294120286634350736906063837462396960, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B2274]
theorem treeEq2273 : B2273.tree = HexagonCover.NBand.M8300_8500.SplitData.node2273 := by
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
  · exact treeEq2274

def B2272 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2273, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq2272 : B2272.tree = HexagonCover.NBand.M8300_8500.SplitData.node2272 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2273
  · rfl

def B2263 : Block := .branch 121 ![578712552117109121, 396317316964419074, 37815825351104580818948, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B2264, (.leaf 5 (Common.fact 256).pointIds 256), B2272]
theorem treeEq2263 : B2263.tree = HexagonCover.NBand.M8300_8500.SplitData.node2263 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2264
  · rfl
  · exact treeEq2272

def B2280 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2280 : B2280.tree = HexagonCover.NBand.M8300_8500.SplitData.node2280 := by
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

def B2279 : Block := .branch 169 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 959).pointIds 959), (.leaf 1 (Common.fact 960).pointIds 960), (.leaf 2 (Common.fact 961).pointIds 961), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B2280, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2279 : B2279.tree = HexagonCover.NBand.M8300_8500.SplitData.node2279 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2280
  · rfl

def B2278 : Block := .branch 163 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B2279]
theorem treeEq2278 : B2278.tree = HexagonCover.NBand.M8300_8500.SplitData.node2278 := by
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
  · exact treeEq2279

def B2277 : Block := .branch 165 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B2278, (.leaf 0 [] 0)]
theorem treeEq2277 : B2277.tree = HexagonCover.NBand.M8300_8500.SplitData.node2277 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2278
  · rfl

def B2276 : Block := .branch 167 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B2277, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2276 : B2276.tree = HexagonCover.NBand.M8300_8500.SplitData.node2276 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2277
  · rfl

def B2262 : Block := .branch 119 ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B2263, B2276, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2262 : B2262.tree = HexagonCover.NBand.M8300_8500.SplitData.node2262 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2263
  · exact treeEq2276
  · rfl
  · rfl

theorem accepted2262 : B2262.accepted = true := by decide +kernel
theorem checked2262 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2262 (maskNeeds ![578712552117109121, 396317316964419074, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq2262]
  exact B2262.sound accepted2262
#print axioms checked2262

end HexagonCover.NBand.M8300_8500.SplitTree.Run0030
