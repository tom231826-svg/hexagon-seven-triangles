import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0010
import HexagonCover.NBand.M7300_7500.SplitTree.Run0011
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0012
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0918_0920 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0920 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0011.checked0920
def B0956 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0956 : B0956.tree = HexagonCover.NBand.M7300_7500.SplitData.node0956 := by
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

def B0955 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0956, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0955 : B0955.tree = HexagonCover.NBand.M7300_7500.SplitData.node0955 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0956
  · rfl
  · rfl

def B0954 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 23384026219072518174516009081983879603233521926208] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0955]
theorem treeEq0954 : B0954.tree = HexagonCover.NBand.M7300_7500.SplitData.node0954 := by
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
  · exact treeEq0955

def B0953 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0954]
theorem treeEq0953 : B0953.tree = HexagonCover.NBand.M7300_7500.SplitData.node0953 := by
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
  · exact treeEq0954

def B0952 : Block := .branch 169 ![2475880078570760549798248833, 737941821641931621890, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515986038083306341688410176] ![B0953, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0952 : B0952.tree = HexagonCover.NBand.M7300_7500.SplitData.node0952 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0953
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0951 : Block := .branch 170 ![2475880078570760549798248833, 737941821641931621890, 2398076729582241716228, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0952, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0951 : B0951.tree = HexagonCover.NBand.M7300_7500.SplitData.node0951 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0952
  · rfl

def B0950 : Block := .branch 171 ![2475880078570760549798248833, 737941821641931621890, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0951, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0950 : B0950.tree = HexagonCover.NBand.M7300_7500.SplitData.node0950 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0951
  · rfl
  · rfl

def B0919 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), Tip0918_0920, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0950]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M7300_7500.SplitData.node0919 := by
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
  · exact treeEq0950

def B0964 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq0964 : B0964.tree = HexagonCover.NBand.M7300_7500.SplitData.node0964 := by
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

def B0963 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0964, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq0963 : B0963.tree = HexagonCover.NBand.M7300_7500.SplitData.node0963 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0964
  · rfl
  · rfl

def B0962 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515932012962879170623634407488] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0963]
theorem treeEq0962 : B0962.tree = HexagonCover.NBand.M7300_7500.SplitData.node0962 := by
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
  · exact treeEq0963

def B0961 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241497972700515692359188544] ![B0962, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0961 : B0961.tree = HexagonCover.NBand.M7300_7500.SplitData.node0961 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0960 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0961]
theorem treeEq0960 : B0960.tree = HexagonCover.NBand.M7300_7500.SplitData.node0960 := by
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
  · exact treeEq0961

def B0959 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438917017082873731800891456] ![B0960, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0959 : B0959.tree = HexagonCover.NBand.M7300_7500.SplitData.node0959 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0960
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0958 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0959, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0958 : B0958.tree = HexagonCover.NBand.M7300_7500.SplitData.node0958 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0959
  · rfl

def B0957 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0958, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0957 : B0957.tree = HexagonCover.NBand.M7300_7500.SplitData.node0957 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0958
  · rfl
  · rfl

def B0918 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 134).pointIds 134), B0919, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0957]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M7300_7500.SplitData.node0918 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0919
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0957

theorem accepted0918 : B0918.accepted = true := by decide +kernel
theorem checked0918 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0918 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq0918]
  exact B0918.sound accepted0918
#print axioms checked0918

def Tip0844_0846 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0846 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0011.checked0846
def B0901 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0901 : B0901.tree = HexagonCover.NBand.M7300_7500.SplitData.node0901 := by
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

def B0900 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0901, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0900 : B0900.tree = HexagonCover.NBand.M7300_7500.SplitData.node0900 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0901
  · rfl
  · rfl

def B0899 : Block := .branch 125 ![385, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0900, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0899 : B0899.tree = HexagonCover.NBand.M7300_7500.SplitData.node0899 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0900
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0898 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 753).pointIds 753), B0899, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0898 : B0898.tree = HexagonCover.NBand.M7300_7500.SplitData.node0898 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0899
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0897 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0898]
theorem treeEq0897 : B0897.tree = HexagonCover.NBand.M7300_7500.SplitData.node0897 := by
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
  · exact treeEq0898

def B0896 : Block := .branch 169 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0897, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0896 : B0896.tree = HexagonCover.NBand.M7300_7500.SplitData.node0896 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0897
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0895 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0896, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M7300_7500.SplitData.node0895 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0896
  · rfl

def B0894 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0895, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M7300_7500.SplitData.node0894 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0895
  · rfl
  · rfl

def B0845 : Block := .branch 80 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0844_0846, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B0894]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M7300_7500.SplitData.node0845 := by
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
  · exact treeEq0894

def B0909 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0909 : B0909.tree = HexagonCover.NBand.M7300_7500.SplitData.node0909 := by
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

def B0908 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0909, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0908 : B0908.tree = HexagonCover.NBand.M7300_7500.SplitData.node0908 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0909
  · rfl
  · rfl

def B0907 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0908]
theorem treeEq0907 : B0907.tree = HexagonCover.NBand.M7300_7500.SplitData.node0907 := by
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
  · exact treeEq0908

def B0906 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B0907, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0906 : B0906.tree = HexagonCover.NBand.M7300_7500.SplitData.node0906 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0907
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0905 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0906]
theorem treeEq0905 : B0905.tree = HexagonCover.NBand.M7300_7500.SplitData.node0905 := by
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
  · exact treeEq0906

def B0904 : Block := .branch 169 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B0905, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0904 : B0904.tree = HexagonCover.NBand.M7300_7500.SplitData.node0904 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0905
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0903 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0904, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0903 : B0903.tree = HexagonCover.NBand.M7300_7500.SplitData.node0903 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0904
  · rfl

def B0902 : Block := .branch 171 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0903, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0902 : B0902.tree = HexagonCover.NBand.M7300_7500.SplitData.node0902 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0903
  · rfl
  · rfl

def B0844 : Block := .branch 78 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B0845, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0902]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M7300_7500.SplitData.node0844 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0845
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0902

theorem accepted0844 : B0844.accepted = true := by decide +kernel
theorem checked0844 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0844 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0844]
  exact B0844.sound accepted0844
#print axioms checked0844

def Tip0712_0787 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0787 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0010.checked0787
def Tip0712_0713 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0713 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0010.checked0713
def B0786 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M7300_7500.SplitData.node0786 := by
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

def B0785 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0786]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M7300_7500.SplitData.node0785 := by
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
  · exact treeEq0786

def B0784 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B0785, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M7300_7500.SplitData.node0784 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0785
  · rfl
  · rfl

def B0783 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), B0784, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M7300_7500.SplitData.node0783 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0784
  · rfl

def B0782 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0783, Tip0712_0787, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M7300_7500.SplitData.node0782 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0783
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0842 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M7300_7500.SplitData.node0842 := by
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

def B0841 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B0842, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M7300_7500.SplitData.node0841 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0842
  · rfl
  · rfl

def B0840 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0841]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M7300_7500.SplitData.node0840 := by
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
  · exact treeEq0841

def B0839 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B0840, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M7300_7500.SplitData.node0839 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0840
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0838 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B0839, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M7300_7500.SplitData.node0838 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0839
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0837 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0838]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M7300_7500.SplitData.node0837 := by
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
  · exact treeEq0838

def B0836 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B0837, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M7300_7500.SplitData.node0836 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0837
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0835 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0836, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M7300_7500.SplitData.node0835 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0836
  · rfl

def B0834 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0835, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M7300_7500.SplitData.node0834 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0835
  · rfl
  · rfl

def B0781 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B0782, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B0834]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M7300_7500.SplitData.node0781 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0782
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0834

def B0780 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0781, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M7300_7500.SplitData.node0780 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0781
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0779 : Block := .branch 113 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0780, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M7300_7500.SplitData.node0779 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0780
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0712 : Block := .branch 76 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0712_0713, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B0779]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M7300_7500.SplitData.node0712 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0779

theorem accepted0712 : B0712.accepted = true := by decide +kernel
theorem checked0712 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0712 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0712]
  exact B0712.sound accepted0712
#print axioms checked0712

def B0988 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M7300_7500.SplitData.node0988 := by
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

def B0987 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0988]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M7300_7500.SplitData.node0987 := by
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
  · exact treeEq0988

def B0986 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0987, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M7300_7500.SplitData.node0986 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0985 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0986]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M7300_7500.SplitData.node0985 := by
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
  · exact treeEq0986

def B0984 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B0985, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M7300_7500.SplitData.node0984 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0985
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0983 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 679).pointIds 679), B0984, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0983 : B0983.tree = HexagonCover.NBand.M7300_7500.SplitData.node0983 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0984
  · rfl

def B0993 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq0993 : B0993.tree = HexagonCover.NBand.M7300_7500.SplitData.node0993 := by
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

def B0992 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0993]
theorem treeEq0992 : B0992.tree = HexagonCover.NBand.M7300_7500.SplitData.node0992 := by
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
  · exact treeEq0993

def B0991 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B0992, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0991 : B0991.tree = HexagonCover.NBand.M7300_7500.SplitData.node0991 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0992
  · rfl
  · rfl

def B0990 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0991, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0990 : B0990.tree = HexagonCover.NBand.M7300_7500.SplitData.node0990 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0991
  · rfl

def B0989 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0990, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0989 : B0989.tree = HexagonCover.NBand.M7300_7500.SplitData.node0989 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0990
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0982 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0983, (.leaf 5 (Common.fact 308).pointIds 308), B0989]
theorem treeEq0982 : B0982.tree = HexagonCover.NBand.M7300_7500.SplitData.node0982 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0983
  · rfl
  · exact treeEq0989

theorem accepted0982 : B0982.accepted = true := by decide +kernel
theorem checked0982 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0982 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0982]
  exact B0982.sound accepted0982
#print axioms checked0982

end HexagonCover.NBand.M7300_7500.SplitTree.Run0012
