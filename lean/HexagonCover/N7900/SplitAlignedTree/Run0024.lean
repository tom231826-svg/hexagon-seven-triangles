import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0024
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B1892 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1892 : B1892.tree = HexagonCover.N7900.SplitData.node1892 := by
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

def B1891 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1892]
theorem treeEq1891 : B1891.tree = HexagonCover.N7900.SplitData.node1891 := by
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
  · exact treeEq1892

def B1890 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1891, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1890 : B1890.tree = HexagonCover.N7900.SplitData.node1890 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1891
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1889 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1890, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1889 : B1889.tree = HexagonCover.N7900.SplitData.node1889 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1890
  · rfl
  · rfl

def B1888 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1889, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1888 : B1888.tree = HexagonCover.N7900.SplitData.node1888 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1889
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1887 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1888, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1887 : B1887.tree = HexagonCover.N7900.SplitData.node1887 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1888
  · rfl

def B1886 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1887, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1886 : B1886.tree = HexagonCover.N7900.SplitData.node1886 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1887
  · rfl
  · rfl

def B1885 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1886]
theorem treeEq1885 : B1885.tree = HexagonCover.N7900.SplitData.node1885 := by
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
  · exact treeEq1886

def B1894 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1894 : B1894.tree = HexagonCover.N7900.SplitData.node1894 := by
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

def B1893 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1894, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1893 : B1893.tree = HexagonCover.N7900.SplitData.node1893 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1894
  · rfl
  · rfl

def B1884 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B1885, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1893]
theorem treeEq1884 : B1884.tree = HexagonCover.N7900.SplitData.node1884 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1885
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1893

def B1901 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq1901 : B1901.tree = HexagonCover.N7900.SplitData.node1901 := by
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

def B1900 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1901]
theorem treeEq1900 : B1900.tree = HexagonCover.N7900.SplitData.node1900 := by
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
  · exact treeEq1901

def B1899 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1900, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1899 : B1899.tree = HexagonCover.N7900.SplitData.node1899 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1900
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1898 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1899, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1898 : B1898.tree = HexagonCover.N7900.SplitData.node1898 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1899
  · rfl
  · rfl

def B1897 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1898, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1897 : B1897.tree = HexagonCover.N7900.SplitData.node1897 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1898
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1896 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1897, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1896 : B1896.tree = HexagonCover.N7900.SplitData.node1896 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1897
  · rfl

def B1895 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1896, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1895 : B1895.tree = HexagonCover.N7900.SplitData.node1895 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1896
  · rfl
  · rfl

def B1883 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1884, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1895]
theorem treeEq1883 : B1883.tree = HexagonCover.N7900.SplitData.node1883 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1884
  · rfl
  · rfl
  · rfl
  · exact treeEq1895

theorem accepted1883 : B1883.accepted = true := by decide +kernel
theorem checked1883 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1883 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1883]
  exact B1883.sound accepted1883
#print axioms checked1883

def Tip1882_1883 : Block := .tip HexagonCover.N7900.SplitData.node1883 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] checked1883
def B1911 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1911 : B1911.tree = HexagonCover.N7900.SplitData.node1911 := by
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

def B1910 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1911]
theorem treeEq1910 : B1910.tree = HexagonCover.N7900.SplitData.node1910 := by
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
  · exact treeEq1911

def B1909 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1910, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1909 : B1909.tree = HexagonCover.N7900.SplitData.node1909 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1910
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1908 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1909, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1908 : B1908.tree = HexagonCover.N7900.SplitData.node1908 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1909
  · rfl
  · rfl

def B1907 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1908, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1907 : B1907.tree = HexagonCover.N7900.SplitData.node1907 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1908
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1906 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1907, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1906 : B1906.tree = HexagonCover.N7900.SplitData.node1906 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1907
  · rfl

def B1905 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1906, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1905 : B1905.tree = HexagonCover.N7900.SplitData.node1905 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1906
  · rfl
  · rfl

def B1904 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1905]
theorem treeEq1904 : B1904.tree = HexagonCover.N7900.SplitData.node1904 := by
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
  · exact treeEq1905

def B1913 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1913 : B1913.tree = HexagonCover.N7900.SplitData.node1913 := by
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

def B1912 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1913, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1912 : B1912.tree = HexagonCover.N7900.SplitData.node1912 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1913
  · rfl
  · rfl

def B1903 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B1904, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1912]
theorem treeEq1903 : B1903.tree = HexagonCover.N7900.SplitData.node1903 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1904
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1912

def B1920 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq1920 : B1920.tree = HexagonCover.N7900.SplitData.node1920 := by
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

def B1919 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1920]
theorem treeEq1919 : B1919.tree = HexagonCover.N7900.SplitData.node1919 := by
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
  · exact treeEq1920

def B1918 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1919, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1918 : B1918.tree = HexagonCover.N7900.SplitData.node1918 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1919
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1917 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1918, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1917 : B1917.tree = HexagonCover.N7900.SplitData.node1917 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1918
  · rfl
  · rfl

def B1916 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1917, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1916 : B1916.tree = HexagonCover.N7900.SplitData.node1916 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1917
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1915 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1916, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1915 : B1915.tree = HexagonCover.N7900.SplitData.node1915 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1916
  · rfl

def B1914 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1915, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1914 : B1914.tree = HexagonCover.N7900.SplitData.node1914 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1915
  · rfl
  · rfl

def B1902 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1903, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1914]
theorem treeEq1902 : B1902.tree = HexagonCover.N7900.SplitData.node1902 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1903
  · rfl
  · rfl
  · rfl
  · exact treeEq1914

def B1882 : Block := .branch 74 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip1882_1883, B1902, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq1882 : B1882.tree = HexagonCover.N7900.SplitData.node1882 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1902
  · rfl
  · rfl
  · rfl

theorem accepted1882 : B1882.accepted = true := by decide +kernel
theorem checked1882 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1882 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1882]
  exact B1882.sound accepted1882
#print axioms checked1882

def B1938 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1938 : B1938.tree = HexagonCover.N7900.SplitData.node1938 := by
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

def B1937 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1938]
theorem treeEq1937 : B1937.tree = HexagonCover.N7900.SplitData.node1937 := by
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
  · exact treeEq1938

def B1936 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1937, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1936 : B1936.tree = HexagonCover.N7900.SplitData.node1936 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1937
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1935 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1936, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1935 : B1935.tree = HexagonCover.N7900.SplitData.node1935 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1936
  · rfl
  · rfl

def B1934 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1935, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1934 : B1934.tree = HexagonCover.N7900.SplitData.node1934 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1935
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1933 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1934, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1933 : B1933.tree = HexagonCover.N7900.SplitData.node1933 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1934
  · rfl

def B1932 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1933, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1932 : B1932.tree = HexagonCover.N7900.SplitData.node1932 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1933
  · rfl
  · rfl

def B1931 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1932]
theorem treeEq1931 : B1931.tree = HexagonCover.N7900.SplitData.node1931 := by
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
  · exact treeEq1932

def B1940 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1940 : B1940.tree = HexagonCover.N7900.SplitData.node1940 := by
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

def B1939 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1940, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1939 : B1939.tree = HexagonCover.N7900.SplitData.node1939 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1940
  · rfl
  · rfl

def B1930 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B1931, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1939]
theorem treeEq1930 : B1930.tree = HexagonCover.N7900.SplitData.node1930 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1931
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1939

def B1947 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq1947 : B1947.tree = HexagonCover.N7900.SplitData.node1947 := by
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

def B1946 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1947]
theorem treeEq1946 : B1946.tree = HexagonCover.N7900.SplitData.node1946 := by
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
  · exact treeEq1947

def B1945 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1946, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1945 : B1945.tree = HexagonCover.N7900.SplitData.node1945 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1946
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1944 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1945, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1944 : B1944.tree = HexagonCover.N7900.SplitData.node1944 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1945
  · rfl
  · rfl

def B1943 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1944, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1943 : B1943.tree = HexagonCover.N7900.SplitData.node1943 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1944
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1942 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1943, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1942 : B1942.tree = HexagonCover.N7900.SplitData.node1942 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1943
  · rfl

def B1941 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1942, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1941 : B1941.tree = HexagonCover.N7900.SplitData.node1941 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1942
  · rfl
  · rfl

def B1929 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1930, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1941]
theorem treeEq1929 : B1929.tree = HexagonCover.N7900.SplitData.node1929 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1930
  · rfl
  · rfl
  · rfl
  · exact treeEq1941

theorem accepted1929 : B1929.accepted = true := by decide +kernel
theorem checked1929 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1929 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1929]
  exact B1929.sound accepted1929
#print axioms checked1929

def B1977 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1977 : B1977.tree = HexagonCover.N7900.SplitData.node1977 := by
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

def B1976 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1977]
theorem treeEq1976 : B1976.tree = HexagonCover.N7900.SplitData.node1976 := by
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
  · exact treeEq1977

def B1975 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1976, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1975 : B1975.tree = HexagonCover.N7900.SplitData.node1975 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1976
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1974 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1975, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1974 : B1974.tree = HexagonCover.N7900.SplitData.node1974 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1975
  · rfl
  · rfl

def B1973 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1974, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1973 : B1973.tree = HexagonCover.N7900.SplitData.node1973 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1974
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1972 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1973, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1972 : B1972.tree = HexagonCover.N7900.SplitData.node1972 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1973
  · rfl

def B1971 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1972, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1971 : B1971.tree = HexagonCover.N7900.SplitData.node1971 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1972
  · rfl
  · rfl

def B1970 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1971]
theorem treeEq1970 : B1970.tree = HexagonCover.N7900.SplitData.node1970 := by
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
  · exact treeEq1971

def B1979 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1979 : B1979.tree = HexagonCover.N7900.SplitData.node1979 := by
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

def B1978 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1979, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1978 : B1978.tree = HexagonCover.N7900.SplitData.node1978 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1979
  · rfl
  · rfl

def B1969 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B1970, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1978]
theorem treeEq1969 : B1969.tree = HexagonCover.N7900.SplitData.node1969 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1970
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1978

def B1986 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq1986 : B1986.tree = HexagonCover.N7900.SplitData.node1986 := by
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

def B1985 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1986]
theorem treeEq1985 : B1985.tree = HexagonCover.N7900.SplitData.node1985 := by
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
  · exact treeEq1986

def B1984 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1985, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1984 : B1984.tree = HexagonCover.N7900.SplitData.node1984 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1985
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1983 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1984, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1983 : B1983.tree = HexagonCover.N7900.SplitData.node1983 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1984
  · rfl
  · rfl

def B1982 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1983, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1982 : B1982.tree = HexagonCover.N7900.SplitData.node1982 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1983
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1981 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1982, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1981 : B1981.tree = HexagonCover.N7900.SplitData.node1981 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1982
  · rfl

def B1980 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1981, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1980 : B1980.tree = HexagonCover.N7900.SplitData.node1980 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1981
  · rfl
  · rfl

def B1968 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1969, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1980]
theorem treeEq1968 : B1968.tree = HexagonCover.N7900.SplitData.node1968 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1969
  · rfl
  · rfl
  · rfl
  · exact treeEq1980

theorem accepted1968 : B1968.accepted = true := by decide +kernel
theorem checked1968 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1968 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1968]
  exact B1968.sound accepted1968
#print axioms checked1968

end HexagonCover.N7900.SplitAlignedTree.Run0024
