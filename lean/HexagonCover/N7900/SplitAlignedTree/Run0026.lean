import HexagonCover.N7900.SplitAlignedTree.Run0025
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0026
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B2063 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2063 : B2063.tree = HexagonCover.N7900.SplitData.node2063 := by
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

def B2062 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2063]
theorem treeEq2062 : B2062.tree = HexagonCover.N7900.SplitData.node2062 := by
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
  · exact treeEq2063

def B2061 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2062, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2061 : B2061.tree = HexagonCover.N7900.SplitData.node2061 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2062
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2060 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2061, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2060 : B2060.tree = HexagonCover.N7900.SplitData.node2060 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2061
  · rfl
  · rfl

def B2059 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2060, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2059 : B2059.tree = HexagonCover.N7900.SplitData.node2059 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2060
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2058 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2059, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2058 : B2058.tree = HexagonCover.N7900.SplitData.node2058 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2059
  · rfl

def B2057 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2058, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2057 : B2057.tree = HexagonCover.N7900.SplitData.node2057 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2058
  · rfl
  · rfl

def B2056 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2057]
theorem treeEq2056 : B2056.tree = HexagonCover.N7900.SplitData.node2056 := by
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
  · exact treeEq2057

def B2065 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2065 : B2065.tree = HexagonCover.N7900.SplitData.node2065 := by
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

def B2064 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2065, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2064 : B2064.tree = HexagonCover.N7900.SplitData.node2064 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2065
  · rfl
  · rfl

def B2055 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2056, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2064]
theorem treeEq2055 : B2055.tree = HexagonCover.N7900.SplitData.node2055 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2056
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2064

def B2072 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2072 : B2072.tree = HexagonCover.N7900.SplitData.node2072 := by
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

def B2071 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2072]
theorem treeEq2071 : B2071.tree = HexagonCover.N7900.SplitData.node2071 := by
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
  · exact treeEq2072

def B2070 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2071, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2070 : B2070.tree = HexagonCover.N7900.SplitData.node2070 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2071
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2069 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2070, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2069 : B2069.tree = HexagonCover.N7900.SplitData.node2069 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2070
  · rfl
  · rfl

def B2068 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2069, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2068 : B2068.tree = HexagonCover.N7900.SplitData.node2068 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2069
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2067 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2068, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2067 : B2067.tree = HexagonCover.N7900.SplitData.node2067 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2068
  · rfl

def B2066 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2067, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2066 : B2066.tree = HexagonCover.N7900.SplitData.node2066 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2067
  · rfl
  · rfl

def B2054 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2055, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2066]
theorem treeEq2054 : B2054.tree = HexagonCover.N7900.SplitData.node2054 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2055
  · rfl
  · rfl
  · rfl
  · exact treeEq2066

theorem accepted2054 : B2054.accepted = true := by decide +kernel
theorem checked2054 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2054 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2054]
  exact B2054.sound accepted2054
#print axioms checked2054

def Tip2014_2015 : Block := .tip HexagonCover.N7900.SplitData.node2015 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] HexagonCover.N7900.SplitAlignedTree.Run0025.checked2015
def B2043 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2043 : B2043.tree = HexagonCover.N7900.SplitData.node2043 := by
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

def B2042 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2043]
theorem treeEq2042 : B2042.tree = HexagonCover.N7900.SplitData.node2042 := by
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
  · exact treeEq2043

def B2041 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2042, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2041 : B2041.tree = HexagonCover.N7900.SplitData.node2041 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2042
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2040 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2041, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2040 : B2040.tree = HexagonCover.N7900.SplitData.node2040 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2041
  · rfl
  · rfl

def B2039 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2040, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2039 : B2039.tree = HexagonCover.N7900.SplitData.node2039 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2040
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2038 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2039, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2038 : B2038.tree = HexagonCover.N7900.SplitData.node2038 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2039
  · rfl

def B2037 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2038, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2037 : B2037.tree = HexagonCover.N7900.SplitData.node2037 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2038
  · rfl
  · rfl

def B2036 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2037]
theorem treeEq2036 : B2036.tree = HexagonCover.N7900.SplitData.node2036 := by
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
  · exact treeEq2037

def B2045 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2045 : B2045.tree = HexagonCover.N7900.SplitData.node2045 := by
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

def B2044 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2045, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2044 : B2044.tree = HexagonCover.N7900.SplitData.node2044 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2045
  · rfl
  · rfl

def B2035 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2036, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2044]
theorem treeEq2035 : B2035.tree = HexagonCover.N7900.SplitData.node2035 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2036
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2044

def B2052 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2052 : B2052.tree = HexagonCover.N7900.SplitData.node2052 := by
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

def B2051 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2052]
theorem treeEq2051 : B2051.tree = HexagonCover.N7900.SplitData.node2051 := by
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
  · exact treeEq2052

def B2050 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2051, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2050 : B2050.tree = HexagonCover.N7900.SplitData.node2050 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2051
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2049 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2050, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2049 : B2049.tree = HexagonCover.N7900.SplitData.node2049 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2050
  · rfl
  · rfl

def B2048 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2049, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2048 : B2048.tree = HexagonCover.N7900.SplitData.node2048 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2049
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2047 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2048, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2047 : B2047.tree = HexagonCover.N7900.SplitData.node2047 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2048
  · rfl

def B2046 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2047, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2046 : B2046.tree = HexagonCover.N7900.SplitData.node2046 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2047
  · rfl
  · rfl

def B2034 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2035, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2046]
theorem treeEq2034 : B2034.tree = HexagonCover.N7900.SplitData.node2034 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2035
  · rfl
  · rfl
  · rfl
  · exact treeEq2046

def B2014 : Block := .branch 74 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip2014_2015, B2034, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq2014 : B2014.tree = HexagonCover.N7900.SplitData.node2014 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2034
  · rfl
  · rfl
  · rfl

theorem accepted2014 : B2014.accepted = true := by decide +kernel
theorem checked2014 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2014 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2014]
  exact B2014.sound accepted2014
#print axioms checked2014

def Tip2053_2054 : Block := .tip HexagonCover.N7900.SplitData.node2054 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked2054
def B2082 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2082 : B2082.tree = HexagonCover.N7900.SplitData.node2082 := by
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

def B2081 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2082]
theorem treeEq2081 : B2081.tree = HexagonCover.N7900.SplitData.node2081 := by
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
  · exact treeEq2082

def B2080 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2081, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2080 : B2080.tree = HexagonCover.N7900.SplitData.node2080 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2081
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2079 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2080, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2079 : B2079.tree = HexagonCover.N7900.SplitData.node2079 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2080
  · rfl
  · rfl

def B2078 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2079, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2078 : B2078.tree = HexagonCover.N7900.SplitData.node2078 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2079
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2077 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2078, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2077 : B2077.tree = HexagonCover.N7900.SplitData.node2077 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2078
  · rfl

def B2076 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2077, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2076 : B2076.tree = HexagonCover.N7900.SplitData.node2076 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2077
  · rfl
  · rfl

def B2075 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2076]
theorem treeEq2075 : B2075.tree = HexagonCover.N7900.SplitData.node2075 := by
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
  · exact treeEq2076

def B2084 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2084 : B2084.tree = HexagonCover.N7900.SplitData.node2084 := by
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

def B2083 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2084, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2083 : B2083.tree = HexagonCover.N7900.SplitData.node2083 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2084
  · rfl
  · rfl

def B2074 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2075, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2083]
theorem treeEq2074 : B2074.tree = HexagonCover.N7900.SplitData.node2074 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2075
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2083

def B2091 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2091 : B2091.tree = HexagonCover.N7900.SplitData.node2091 := by
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

def B2090 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2091]
theorem treeEq2090 : B2090.tree = HexagonCover.N7900.SplitData.node2090 := by
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
  · exact treeEq2091

def B2089 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2090, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2089 : B2089.tree = HexagonCover.N7900.SplitData.node2089 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2090
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2088 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2089, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2088 : B2088.tree = HexagonCover.N7900.SplitData.node2088 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2089
  · rfl
  · rfl

def B2087 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2088, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2087 : B2087.tree = HexagonCover.N7900.SplitData.node2087 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2088
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2086 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2087, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2086 : B2086.tree = HexagonCover.N7900.SplitData.node2086 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2087
  · rfl

def B2085 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2086, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2085 : B2085.tree = HexagonCover.N7900.SplitData.node2085 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2086
  · rfl
  · rfl

def B2073 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2074, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2085]
theorem treeEq2073 : B2073.tree = HexagonCover.N7900.SplitData.node2073 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2074
  · rfl
  · rfl
  · rfl
  · exact treeEq2085

def B2053 : Block := .branch 74 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip2053_2054, B2073, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq2053 : B2053.tree = HexagonCover.N7900.SplitData.node2053 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2073
  · rfl
  · rfl
  · rfl

theorem accepted2053 : B2053.accepted = true := by decide +kernel
theorem checked2053 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2053 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2053]
  exact B2053.sound accepted2053
#print axioms checked2053

def B2103 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2103 : B2103.tree = HexagonCover.N7900.SplitData.node2103 := by
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

def B2102 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2103]
theorem treeEq2102 : B2102.tree = HexagonCover.N7900.SplitData.node2102 := by
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
  · exact treeEq2103

def B2101 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2102, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2101 : B2101.tree = HexagonCover.N7900.SplitData.node2101 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2102
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2100 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2101, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2100 : B2100.tree = HexagonCover.N7900.SplitData.node2100 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2101
  · rfl
  · rfl

def B2099 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B2100, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2099 : B2099.tree = HexagonCover.N7900.SplitData.node2099 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2100
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2098 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B2099, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2098 : B2098.tree = HexagonCover.N7900.SplitData.node2098 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2099
  · rfl

def B2097 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B2098, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2097 : B2097.tree = HexagonCover.N7900.SplitData.node2097 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2098
  · rfl
  · rfl

def B2096 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B2097]
theorem treeEq2096 : B2096.tree = HexagonCover.N7900.SplitData.node2096 := by
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
  · exact treeEq2097

def B2105 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq2105 : B2105.tree = HexagonCover.N7900.SplitData.node2105 := by
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

def B2104 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2105, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2104 : B2104.tree = HexagonCover.N7900.SplitData.node2104 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2105
  · rfl
  · rfl

def B2095 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B2096, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2104]
theorem treeEq2095 : B2095.tree = HexagonCover.N7900.SplitData.node2095 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2096
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2104

def B2112 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq2112 : B2112.tree = HexagonCover.N7900.SplitData.node2112 := by
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

def B2111 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B2112]
theorem treeEq2111 : B2111.tree = HexagonCover.N7900.SplitData.node2111 := by
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
  · exact treeEq2112

def B2110 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2111, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq2110 : B2110.tree = HexagonCover.N7900.SplitData.node2110 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2111
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2109 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2110, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq2109 : B2109.tree = HexagonCover.N7900.SplitData.node2109 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2110
  · rfl
  · rfl

def B2108 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B2109, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq2108 : B2108.tree = HexagonCover.N7900.SplitData.node2108 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2109
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2107 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B2108, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq2107 : B2107.tree = HexagonCover.N7900.SplitData.node2107 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2108
  · rfl

def B2106 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2107, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq2106 : B2106.tree = HexagonCover.N7900.SplitData.node2106 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2107
  · rfl
  · rfl

def B2094 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B2095, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B2106]
theorem treeEq2094 : B2094.tree = HexagonCover.N7900.SplitData.node2094 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2095
  · rfl
  · rfl
  · rfl
  · exact treeEq2106

theorem accepted2094 : B2094.accepted = true := by decide +kernel
theorem checked2094 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node2094 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq2094]
  exact B2094.sound accepted2094
#print axioms checked2094

end HexagonCover.N7900.SplitAlignedTree.Run0026
