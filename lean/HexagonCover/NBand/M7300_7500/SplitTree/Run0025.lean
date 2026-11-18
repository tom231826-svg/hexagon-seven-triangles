import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0024
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0025
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip1844_1846 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1846 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0024.checked1846
def B1865 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1865 : B1865.tree = HexagonCover.NBand.M7300_7500.SplitData.node1865 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1864 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B1865, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq1864 : B1864.tree = HexagonCover.NBand.M7300_7500.SplitData.node1864 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1865
  · rfl
  · rfl

def B1863 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B1864, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1863 : B1863.tree = HexagonCover.NBand.M7300_7500.SplitData.node1863 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1864
  · rfl

def B1862 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1863]
theorem treeEq1862 : B1862.tree = HexagonCover.NBand.M7300_7500.SplitData.node1862 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1863

def B1861 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B1862, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1861 : B1861.tree = HexagonCover.NBand.M7300_7500.SplitData.node1861 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1862
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1860 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1861]
theorem treeEq1860 : B1860.tree = HexagonCover.NBand.M7300_7500.SplitData.node1860 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1861

def B1859 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739815242086773067913625664] ![B1860, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1859 : B1859.tree = HexagonCover.NBand.M7300_7500.SplitData.node1859 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1860
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1858 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1859, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1858 : B1858.tree = HexagonCover.NBand.M7300_7500.SplitData.node1858 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1859
  · rfl

def B1857 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1858, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1857 : B1857.tree = HexagonCover.NBand.M7300_7500.SplitData.node1857 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1858
  · rfl
  · rfl

def B1845 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip1844_1846, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1857]
theorem treeEq1845 : B1845.tree = HexagonCover.NBand.M7300_7500.SplitData.node1845 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1857

def B1873 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1873 : B1873.tree = HexagonCover.NBand.M7300_7500.SplitData.node1873 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1872 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1873, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1872 : B1872.tree = HexagonCover.NBand.M7300_7500.SplitData.node1872 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1873
  · rfl
  · rfl

def B1871 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1872]
theorem treeEq1871 : B1871.tree = HexagonCover.NBand.M7300_7500.SplitData.node1871 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1872

def B1870 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B1871, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1870 : B1870.tree = HexagonCover.NBand.M7300_7500.SplitData.node1870 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1871
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1869 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1870]
theorem treeEq1869 : B1869.tree = HexagonCover.NBand.M7300_7500.SplitData.node1869 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1870

def B1868 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1869, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1868 : B1868.tree = HexagonCover.NBand.M7300_7500.SplitData.node1868 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1869
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1867 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1868, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1867 : B1867.tree = HexagonCover.NBand.M7300_7500.SplitData.node1867 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1868
  · rfl

def B1866 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1867, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1866 : B1866.tree = HexagonCover.NBand.M7300_7500.SplitData.node1866 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1867
  · rfl
  · rfl

def B1844 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 86).pointIds 86), B1845, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1866]
theorem treeEq1844 : B1844.tree = HexagonCover.NBand.M7300_7500.SplitData.node1844 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1845
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1866

theorem accepted1844 : B1844.accepted = true := by decide +kernel
theorem checked1844 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1844 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1844]
  exact B1844.sound accepted1844
#print axioms checked1844

def Tip1842_1844 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1844 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1844
def B1880 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1880 : B1880.tree = HexagonCover.NBand.M7300_7500.SplitData.node1880 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1879 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1880, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq1879 : B1879.tree = HexagonCover.NBand.M7300_7500.SplitData.node1879 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1880
  · rfl
  · rfl

def B1878 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 23384026219072518174516009081983879603233521926208] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1879]
theorem treeEq1878 : B1878.tree = HexagonCover.NBand.M7300_7500.SplitData.node1878 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1879

def B1877 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1878]
theorem treeEq1877 : B1877.tree = HexagonCover.NBand.M7300_7500.SplitData.node1877 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1878

def B1876 : Block := .branch 169 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515986038083306341688410176] ![B1877, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1876 : B1876.tree = HexagonCover.NBand.M7300_7500.SplitData.node1876 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1877
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1875 : Block := .branch 170 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1876, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1875 : B1875.tree = HexagonCover.NBand.M7300_7500.SplitData.node1875 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1876
  · rfl

def B1874 : Block := .branch 171 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1875, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1874 : B1874.tree = HexagonCover.NBand.M7300_7500.SplitData.node1874 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1875
  · rfl
  · rfl

def B1843 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), Tip1842_1844, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B1874]
theorem treeEq1843 : B1843.tree = HexagonCover.NBand.M7300_7500.SplitData.node1843 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1874

def B1888 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq1888 : B1888.tree = HexagonCover.NBand.M7300_7500.SplitData.node1888 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1887 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1888, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq1887 : B1887.tree = HexagonCover.NBand.M7300_7500.SplitData.node1887 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1888
  · rfl
  · rfl

def B1886 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515932012962879170623634407488] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1887]
theorem treeEq1886 : B1886.tree = HexagonCover.NBand.M7300_7500.SplitData.node1886 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1887

def B1885 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241497972700515692359188544] ![B1886, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1885 : B1885.tree = HexagonCover.NBand.M7300_7500.SplitData.node1885 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1886
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1884 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1885]
theorem treeEq1884 : B1884.tree = HexagonCover.NBand.M7300_7500.SplitData.node1884 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1885

def B1883 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438917017082873731800891456] ![B1884, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1883 : B1883.tree = HexagonCover.NBand.M7300_7500.SplitData.node1883 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1884
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1882 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1883, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1882 : B1882.tree = HexagonCover.NBand.M7300_7500.SplitData.node1882 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1883
  · rfl

def B1881 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1882, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq1881 : B1881.tree = HexagonCover.NBand.M7300_7500.SplitData.node1881 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1882
  · rfl
  · rfl

def B1842 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 134).pointIds 134), B1843, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B1881]
theorem treeEq1842 : B1842.tree = HexagonCover.NBand.M7300_7500.SplitData.node1842 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1843
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1881

theorem accepted1842 : B1842.accepted = true := by decide +kernel
theorem checked1842 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1842 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1842]
  exact B1842.sound accepted1842
#print axioms checked1842

def Tip1768_1770 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1770 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0024.checked1770
def B1825 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1825 : B1825.tree = HexagonCover.NBand.M7300_7500.SplitData.node1825 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1824 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1825, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq1824 : B1824.tree = HexagonCover.NBand.M7300_7500.SplitData.node1824 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1825
  · rfl
  · rfl

def B1823 : Block := .branch 125 ![385, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B1824, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1823 : B1823.tree = HexagonCover.NBand.M7300_7500.SplitData.node1823 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1824
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1822 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 753).pointIds 753), B1823, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1822 : B1822.tree = HexagonCover.NBand.M7300_7500.SplitData.node1822 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1823
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1821 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1822]
theorem treeEq1821 : B1821.tree = HexagonCover.NBand.M7300_7500.SplitData.node1821 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1822

def B1820 : Block := .branch 169 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B1821, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1820 : B1820.tree = HexagonCover.NBand.M7300_7500.SplitData.node1820 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1821
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1819 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1820, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1819 : B1819.tree = HexagonCover.NBand.M7300_7500.SplitData.node1819 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1820
  · rfl

def B1818 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1819, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq1818 : B1818.tree = HexagonCover.NBand.M7300_7500.SplitData.node1818 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1819
  · rfl
  · rfl

def B1769 : Block := .branch 80 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1768_1770, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B1818]
theorem treeEq1769 : B1769.tree = HexagonCover.NBand.M7300_7500.SplitData.node1769 := by
  change Tree.branch (80 : Fin 172) _ = Tree.branch (80 : Fin 172) _
  apply congrArg (Tree.branch (80 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1818

def B1833 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1833 : B1833.tree = HexagonCover.NBand.M7300_7500.SplitData.node1833 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1832 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1833, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1832 : B1832.tree = HexagonCover.NBand.M7300_7500.SplitData.node1832 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1833
  · rfl
  · rfl

def B1831 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1832]
theorem treeEq1831 : B1831.tree = HexagonCover.NBand.M7300_7500.SplitData.node1831 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1832

def B1830 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B1831, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1830 : B1830.tree = HexagonCover.NBand.M7300_7500.SplitData.node1830 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1831
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1829 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1830]
theorem treeEq1829 : B1829.tree = HexagonCover.NBand.M7300_7500.SplitData.node1829 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1830

def B1828 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B1829, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1828 : B1828.tree = HexagonCover.NBand.M7300_7500.SplitData.node1828 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1829
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1827 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1828, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1827 : B1827.tree = HexagonCover.NBand.M7300_7500.SplitData.node1827 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1828
  · rfl

def B1826 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1827, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1826 : B1826.tree = HexagonCover.NBand.M7300_7500.SplitData.node1826 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1827
  · rfl
  · rfl

def B1768 : Block := .branch 78 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B1769, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B1826]
theorem treeEq1768 : B1768.tree = HexagonCover.NBand.M7300_7500.SplitData.node1768 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1769
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1826

theorem accepted1768 : B1768.accepted = true := by decide +kernel
theorem checked1768 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1768 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1768]
  exact B1768.sound accepted1768
#print axioms checked1768

def B1911 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq1911 : B1911.tree = HexagonCover.NBand.M7300_7500.SplitData.node1911 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1910 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1911]
theorem treeEq1910 : B1910.tree = HexagonCover.NBand.M7300_7500.SplitData.node1910 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1911

def B1909 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B1910, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1909 : B1909.tree = HexagonCover.NBand.M7300_7500.SplitData.node1909 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1910
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1908 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1909]
theorem treeEq1908 : B1908.tree = HexagonCover.NBand.M7300_7500.SplitData.node1908 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1909

def B1907 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B1908, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1907 : B1907.tree = HexagonCover.NBand.M7300_7500.SplitData.node1907 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1908
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1906 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 679).pointIds 679), B1907, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1906 : B1906.tree = HexagonCover.NBand.M7300_7500.SplitData.node1906 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1907
  · rfl

def B1916 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq1916 : B1916.tree = HexagonCover.NBand.M7300_7500.SplitData.node1916 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1915 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1916]
theorem treeEq1915 : B1915.tree = HexagonCover.NBand.M7300_7500.SplitData.node1915 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1916

def B1914 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B1915, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1914 : B1914.tree = HexagonCover.NBand.M7300_7500.SplitData.node1914 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1915
  · rfl
  · rfl

def B1913 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B1914, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1913 : B1913.tree = HexagonCover.NBand.M7300_7500.SplitData.node1913 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1914
  · rfl

def B1912 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B1913, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq1912 : B1912.tree = HexagonCover.NBand.M7300_7500.SplitData.node1912 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1913
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1905 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B1906, (.leaf 5 (Common.fact 308).pointIds 308), B1912]
theorem treeEq1905 : B1905.tree = HexagonCover.NBand.M7300_7500.SplitData.node1905 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1906
  · rfl
  · exact treeEq1912

theorem accepted1905 : B1905.accepted = true := by decide +kernel
theorem checked1905 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1905 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1905]
  exact B1905.sound accepted1905
#print axioms checked1905

end HexagonCover.NBand.M7300_7500.SplitTree.Run0025
