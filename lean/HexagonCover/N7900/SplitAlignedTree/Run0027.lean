import HexagonCover.N7900.SplitAlignedTree.Run0025
import HexagonCover.N7900.SplitAlignedTree.Run0026
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0027
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B2142 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2142 : B2142.tree = HexagonCover.N7900.SplitData.node2142 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2141 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2142]
theorem treeEq2141 : B2141.tree = HexagonCover.N7900.SplitData.node2141 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2142

def B2140 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2141, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2140 : B2140.tree = HexagonCover.N7900.SplitData.node2140 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2141
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2139 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2140, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2139 : B2139.tree = HexagonCover.N7900.SplitData.node2139 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2140
  · rfl
  · rfl

def B2138 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2139, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2138 : B2138.tree = HexagonCover.N7900.SplitData.node2138 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2139
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2137 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2138, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2137 : B2137.tree = HexagonCover.N7900.SplitData.node2137 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2138
  · rfl

def B2136 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2137, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2136 : B2136.tree = HexagonCover.N7900.SplitData.node2136 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2137
  · rfl
  · rfl

def B2135 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2136]
theorem treeEq2135 : B2135.tree = HexagonCover.N7900.SplitData.node2135 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2136

def B2144 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2144 : B2144.tree = HexagonCover.N7900.SplitData.node2144 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2143 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2144, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2143 : B2143.tree = HexagonCover.N7900.SplitData.node2143 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2144
  · rfl
  · rfl

def B2134 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2135, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2143]
theorem treeEq2134 : B2134.tree = HexagonCover.N7900.SplitData.node2134 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2135
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2143

def B2151 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2151 : B2151.tree = HexagonCover.N7900.SplitData.node2151 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2150 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2151]
theorem treeEq2150 : B2150.tree = HexagonCover.N7900.SplitData.node2150 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2151

def B2149 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2150, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2149 : B2149.tree = HexagonCover.N7900.SplitData.node2149 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2148 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2149, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2148 : B2148.tree = HexagonCover.N7900.SplitData.node2148 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2149
  · rfl
  · rfl

def B2147 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2148, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2147 : B2147.tree = HexagonCover.N7900.SplitData.node2147 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2148
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2146 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2147, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2146 : B2146.tree = HexagonCover.N7900.SplitData.node2146 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2147
  · rfl

def B2145 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2146, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2145 : B2145.tree = HexagonCover.N7900.SplitData.node2145 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2146
  · rfl
  · rfl

def B2133 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2134, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2145]
theorem treeEq2133 : B2133.tree = HexagonCover.N7900.SplitData.node2133 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2134
  · rfl
  · rfl
  · rfl
  · exact treeEq2145

theorem accepted2133 : B2133.accepted = true := by decide +kernel
theorem checked2133 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2133 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2133]
  exact B2133.sound accepted2133
#print axioms checked2133

def Tip2093_2094 : Block := .tip HexagonCover.N7900.SplitData.node2094 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0026.checked2094
def B2122 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2122 : B2122.tree = HexagonCover.N7900.SplitData.node2122 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2121 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2122]
theorem treeEq2121 : B2121.tree = HexagonCover.N7900.SplitData.node2121 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2122

def B2120 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2121, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2120 : B2120.tree = HexagonCover.N7900.SplitData.node2120 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2121
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2119 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2120, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2119 : B2119.tree = HexagonCover.N7900.SplitData.node2119 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2120
  · rfl
  · rfl

def B2118 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2119, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2118 : B2118.tree = HexagonCover.N7900.SplitData.node2118 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2119
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2117 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2118, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2117 : B2117.tree = HexagonCover.N7900.SplitData.node2117 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2118
  · rfl

def B2116 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2117, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2116 : B2116.tree = HexagonCover.N7900.SplitData.node2116 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2117
  · rfl
  · rfl

def B2115 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2116]
theorem treeEq2115 : B2115.tree = HexagonCover.N7900.SplitData.node2115 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2116

def B2124 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2124 : B2124.tree = HexagonCover.N7900.SplitData.node2124 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2123 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2124, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2123 : B2123.tree = HexagonCover.N7900.SplitData.node2123 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2124
  · rfl
  · rfl

def B2114 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2115, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2123]
theorem treeEq2114 : B2114.tree = HexagonCover.N7900.SplitData.node2114 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2115
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2123

def B2131 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2131 : B2131.tree = HexagonCover.N7900.SplitData.node2131 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2130 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2131]
theorem treeEq2130 : B2130.tree = HexagonCover.N7900.SplitData.node2130 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2131

def B2129 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2130, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2129 : B2129.tree = HexagonCover.N7900.SplitData.node2129 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2128 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2129, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2128 : B2128.tree = HexagonCover.N7900.SplitData.node2128 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2129
  · rfl
  · rfl

def B2127 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2128, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2127 : B2127.tree = HexagonCover.N7900.SplitData.node2127 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2126 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2127, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2126 : B2126.tree = HexagonCover.N7900.SplitData.node2126 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2127
  · rfl

def B2125 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2126, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2125 : B2125.tree = HexagonCover.N7900.SplitData.node2125 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2126
  · rfl
  · rfl

def B2113 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2114, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2125]
theorem treeEq2113 : B2113.tree = HexagonCover.N7900.SplitData.node2113 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2114
  · rfl
  · rfl
  · rfl
  · exact treeEq2125

def B2093 : Block := .branch 74 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip2093_2094, B2113, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq2093 : B2093.tree = HexagonCover.N7900.SplitData.node2093 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2113
  · rfl
  · rfl
  · rfl

theorem accepted2093 : B2093.accepted = true := by decide +kernel
theorem checked2093 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2093 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2093]
  exact B2093.sound accepted2093
#print axioms checked2093

def Tip2132_2133 : Block := .tip HexagonCover.N7900.SplitData.node2133 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked2133
def B2161 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2161 : B2161.tree = HexagonCover.N7900.SplitData.node2161 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2160 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2161]
theorem treeEq2160 : B2160.tree = HexagonCover.N7900.SplitData.node2160 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2161

def B2159 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2160, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2159 : B2159.tree = HexagonCover.N7900.SplitData.node2159 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2160
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2158 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2159, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2158 : B2158.tree = HexagonCover.N7900.SplitData.node2158 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2159
  · rfl
  · rfl

def B2157 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2158, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2157 : B2157.tree = HexagonCover.N7900.SplitData.node2157 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2158
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2156 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2157, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2156 : B2156.tree = HexagonCover.N7900.SplitData.node2156 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2157
  · rfl

def B2155 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2156, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2155 : B2155.tree = HexagonCover.N7900.SplitData.node2155 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2156
  · rfl
  · rfl

def B2154 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2155]
theorem treeEq2154 : B2154.tree = HexagonCover.N7900.SplitData.node2154 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2155

def B2163 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2163 : B2163.tree = HexagonCover.N7900.SplitData.node2163 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2162 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2163, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2162 : B2162.tree = HexagonCover.N7900.SplitData.node2162 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2163
  · rfl
  · rfl

def B2153 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2154, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2162]
theorem treeEq2153 : B2153.tree = HexagonCover.N7900.SplitData.node2153 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2154
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2162

def B2170 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2170 : B2170.tree = HexagonCover.N7900.SplitData.node2170 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2169 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2170]
theorem treeEq2169 : B2169.tree = HexagonCover.N7900.SplitData.node2169 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2170

def B2168 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2169, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2168 : B2168.tree = HexagonCover.N7900.SplitData.node2168 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2169
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2167 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2168, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2167 : B2167.tree = HexagonCover.N7900.SplitData.node2167 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2168
  · rfl
  · rfl

def B2166 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2167, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2166 : B2166.tree = HexagonCover.N7900.SplitData.node2166 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2167
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2165 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2166, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2165 : B2165.tree = HexagonCover.N7900.SplitData.node2165 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2166
  · rfl

def B2164 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2165, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2164 : B2164.tree = HexagonCover.N7900.SplitData.node2164 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2165
  · rfl
  · rfl

def B2152 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2153, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2164]
theorem treeEq2152 : B2152.tree = HexagonCover.N7900.SplitData.node2152 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2153
  · rfl
  · rfl
  · rfl
  · exact treeEq2164

def B2132 : Block := .branch 74 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip2132_2133, B2152, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq2132 : B2132.tree = HexagonCover.N7900.SplitData.node2132 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2152
  · rfl
  · rfl
  · rfl

theorem accepted2132 : B2132.accepted = true := by decide +kernel
theorem checked2132 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2132 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2132]
  exact B2132.sound accepted2132
#print axioms checked2132

def Tip1734_1928 : Block := .tip HexagonCover.N7900.SplitData.node1928 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0025.checked1928
def Tip1734_1967 : Block := .tip HexagonCover.N7900.SplitData.node1967 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0025.checked1967
def Tip1734_1736 : Block := .tip HexagonCover.N7900.SplitData.node1736 ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0025.checked1736
def Tip1734_2014 : Block := .tip HexagonCover.N7900.SplitData.node2014 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0026.checked2014
def Tip1734_2053 : Block := .tip HexagonCover.N7900.SplitData.node2053 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0026.checked2053
def Tip1734_2093 : Block := .tip HexagonCover.N7900.SplitData.node2093 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked2093
def Tip1734_2132 : Block := .tip HexagonCover.N7900.SplitData.node2132 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked2132
def B1927 : Block := .branch 73 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1734_1928, Tip1734_1967, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq1927 : B1927.tree = HexagonCover.N7900.SplitData.node1927 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2007 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2007 : B2007.tree = HexagonCover.N7900.SplitData.node2007 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2006 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2007, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq2006 : B2006.tree = HexagonCover.N7900.SplitData.node2006 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2007
  · rfl
  · rfl

def B1926 : Block := .branch 68 ![10394734921871481092272966284083585, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 757).pointIds 757), B1927, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B2006]
theorem treeEq1926 : B1926.tree = HexagonCover.N7900.SplitData.node1926 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1927
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2006

def B1925 : Block := .branch 113 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B1926, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1925 : B1925.tree = HexagonCover.N7900.SplitData.node1925 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1926
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1924 : Block := .branch 144 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1925, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1924 : B1924.tree = HexagonCover.N7900.SplitData.node1924 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1925
  · rfl

def B1923 : Block := .branch 161 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38690348594151003235835912, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 694).pointIds 694), (.leaf 3 (Common.fact 675).pointIds 675), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B1924]
theorem treeEq1923 : B1923.tree = HexagonCover.N7900.SplitData.node1923 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1924

def B1735 : Block := .branch 72 ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), Tip1734_1736, B1923, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq1735 : B1735.tree = HexagonCover.N7900.SplitData.node1735 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1923
  · rfl
  · rfl
  · rfl

def B2013 : Block := .branch 73 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1734_2014, Tip1734_2053, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq2013 : B2013.tree = HexagonCover.N7900.SplitData.node2013 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2092 : Block := .branch 73 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip1734_2093, Tip1734_2132, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq2092 : B2092.tree = HexagonCover.N7900.SplitData.node2092 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2012 : Block := .branch 72 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), B2013, B2092, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq2012 : B2012.tree = HexagonCover.N7900.SplitData.node2012 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2013
  · exact treeEq2092
  · rfl
  · rfl
  · rfl

def B2172 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2172 : B2172.tree = HexagonCover.N7900.SplitData.node2172 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2171 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2172, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq2171 : B2171.tree = HexagonCover.N7900.SplitData.node2171 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2172
  · rfl
  · rfl

def B2011 : Block := .branch 68 ![10394734921871481092272966284083585, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 757).pointIds 757), B2012, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B2171]
theorem treeEq2011 : B2011.tree = HexagonCover.N7900.SplitData.node2011 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2012
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2171

def B2010 : Block := .branch 113 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![B2011, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq2010 : B2010.tree = HexagonCover.N7900.SplitData.node2010 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2009 : Block := .branch 144 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B2010, (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2009 : B2009.tree = HexagonCover.N7900.SplitData.node2009 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2010
  · rfl

def B2008 : Block := .branch 161 ![10141204801825835211973625643393, 147718067777752270338, 9223512774343137284, 38687987410909568413229064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 694).pointIds 694), (.leaf 3 (Common.fact 676).pointIds 676), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B2009]
theorem treeEq2008 : B2008.tree = HexagonCover.N7900.SplitData.node2008 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2009

def B1734 : Block := .branch 71 ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), B1735, B2008, (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq1734 : B1734.tree = HexagonCover.N7900.SplitData.node1734 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1735
  · exact treeEq2008
  · rfl
  · rfl
  · rfl

theorem accepted1734 : B1734.accepted = true := by decide +kernel
theorem checked1734 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1734 (maskNeeds ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1734]
  exact B1734.sound accepted1734
#print axioms checked1734

end HexagonCover.N7900.SplitAlignedTree.Run0027
