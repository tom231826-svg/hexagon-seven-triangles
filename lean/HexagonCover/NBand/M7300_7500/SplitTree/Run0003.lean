import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0255_0257 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0257 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] HexagonCover.NBand.M7300_7500.SplitTree.Run0002.checked0257
def B0298 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M7300_7500.SplitData.node0298 := by
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

def B0297 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0298, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M7300_7500.SplitData.node0297 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl
  · rfl

def B0296 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 23384026219072518174516009081983879603233521926208] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0297]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M7300_7500.SplitData.node0296 := by
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
  · exact treeEq0297

def B0295 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0296]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M7300_7500.SplitData.node0295 := by
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
  · exact treeEq0296

def B0294 : Block := .branch 169 ![2475880078570760549798248833, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257051758523351288738601238592] ![B0295, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M7300_7500.SplitData.node0294 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0293 : Block := .branch 170 ![10384596192949733827821542456689025, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B0294, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M7300_7500.SplitData.node0293 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0294
  · rfl

def B0292 : Block := .branch 171 ![10384596192949733827821542456689025, 737941821641931621890, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), B0293, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M7300_7500.SplitData.node0292 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl
  · rfl

def B0256 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), Tip0255_0257, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0292]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M7300_7500.SplitData.node0256 := by
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
  · exact treeEq0292

def B0306 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M7300_7500.SplitData.node0306 := by
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

def B0305 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0306, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M7300_7500.SplitData.node0305 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0306
  · rfl
  · rfl

def B0304 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515932012962879170623634407488] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0305]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M7300_7500.SplitData.node0304 := by
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
  · exact treeEq0305

def B0303 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241497972700515692359188544] ![B0304, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M7300_7500.SplitData.node0303 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0304
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0302 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0303]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M7300_7500.SplitData.node0302 := by
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
  · exact treeEq0303

def B0301 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![B0302, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M7300_7500.SplitData.node0301 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0302
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0300 : Block := .branch 170 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B0301, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M7300_7500.SplitData.node0300 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0301
  · rfl

def B0299 : Block := .branch 171 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), B0300, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M7300_7500.SplitData.node0299 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0300
  · rfl
  · rfl

def B0255 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 134).pointIds 134), B0256, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0299]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M7300_7500.SplitData.node0255 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0256
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0299

theorem accepted0255 : B0255.accepted = true := by decide +kernel
theorem checked0255 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0255 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384]) := by
  rw [← treeEq0255]
  exact B0255.sound accepted0255
#print axioms checked0255

def Tip0239_0255 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0255 ![10384596192949733827821542456689025, 738230052018083333634, 21306025433931551086596, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] checked0255
def B0254 : Block := .branch 79 ![374144419156732419900372734364752838285738251387265, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 677).pointIds 677), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M7300_7500.SplitData.node0254 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0253 : Block := .branch 159 ![374144419156732419900372734364752838285738251387265, 1099511629314, 6148, 24584, 98320, 393248, 2993155353276147812698245388717145269422684804481088] ![(.leaf 0 (Common.fact 674).pointIds 674), B0254, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M7300_7500.SplitData.node0253 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0254
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0252 : Block := .branch 124 ![374144419156711152252440175710786377372773765874049, 1099511629314, 6148, 24584, 98320, 393248, 2993155353276147812698245388717145269422684804481088] ![B0253, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M7300_7500.SplitData.node0252 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0253
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0251 : Block := .branch 129 ![374144419156711152252440175710786377372773765874049, 1099511629314, 6148, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 301).pointIds 301), B0252]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M7300_7500.SplitData.node0251 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0252

def B0250 : Block := .branch 130 ![374144419156711152252440175710786377372773765874049, 1099511629314, 6148, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 488).pointIds 488), (.leaf 1 (Common.fact 489).pointIds 489), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 671).pointIds 671), (.leaf 5 (Common.fact 493).pointIds 493), B0251]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M7300_7500.SplitData.node0250 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251

def B0249 : Block := .branch 86 ![374144419156711152252440175710786377372773765874049, 1099511629314, 18482772870728521732, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0250, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M7300_7500.SplitData.node0249 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0250
  · rfl
  · rfl
  · rfl

def B0248 : Block := .branch 89 ![374144419156711152252440175710786377372773765874049, 1099511629314, 18482772870728521732, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 86).pointIds 86), B0249, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M7300_7500.SplitData.node0248 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0247 : Block := .branch 112 ![374144419156711147060143317175958748842277436653953, 1099511629314, 18482772870728521732, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B0248, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M7300_7500.SplitData.node0247 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0248
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0246 : Block := .branch 118 ![374144419156711147060143317175958748842277436653953, 1099511629314, 18482772870728521732, 79228162514264337593543974920, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), B0247, (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M7300_7500.SplitData.node0246 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 75 ![374144419156711147060143317175958748842277436653953, 1099511629314, 18482772870728521732, 5846006549323611672894006179005624084350864744456, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B0246, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M7300_7500.SplitData.node0245 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0246
  · rfl
  · rfl
  · rfl
  · rfl

def B0244 : Block := .branch 162 ![374144419156711147060143317175958748842277436653953, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0245, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M7300_7500.SplitData.node0244 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl
  · rfl
  · rfl

def B0243 : Block := .branch 168 ![590295810358705652097, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![B0244, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M7300_7500.SplitData.node0243 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0244
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0242 : Block := .branch 171 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 652).pointIds 652), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 654).pointIds 654), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0243]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M7300_7500.SplitData.node0242 := by
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
  · exact treeEq0243

def B0241 : Block := .branch 170 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 648).pointIds 648), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 623).pointIds 623), B0242, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M7300_7500.SplitData.node0241 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0242
  · rfl
  · rfl

def B0240 : Block := .branch 169 ![10384596192950324123631901162340737, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B0241, (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M7300_7500.SplitData.node0240 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl

def B0239 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384] ![B0240, Tip0239_0255, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M7300_7500.SplitData.node0239 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0240
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0239 : B0239.accepted = true := by decide +kernel
theorem checked0239 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0239 (maskNeeds ![10384596192949733827821542456689025, 147934241659377681922, 21306025433931551086596, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257283872280717297540144824384]) := by
  rw [← treeEq0239]
  exact B0239.sound accepted0239
#print axioms checked0239

def B0329 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M7300_7500.SplitData.node0329 := by
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

def B0328 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0329]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M7300_7500.SplitData.node0328 := by
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
  · exact treeEq0329

def B0327 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0328, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M7300_7500.SplitData.node0327 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0328
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0326 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0327]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M7300_7500.SplitData.node0326 := by
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
  · exact treeEq0327

def B0325 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B0326, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M7300_7500.SplitData.node0325 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0326
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0324 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 679).pointIds 679), B0325, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M7300_7500.SplitData.node0324 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0325
  · rfl

def B0334 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M7300_7500.SplitData.node0334 := by
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

def B0333 : Block := .branch 171 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0334]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M7300_7500.SplitData.node0333 := by
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
  · exact treeEq0334

def B0332 : Block := .branch 170 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), B0333, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M7300_7500.SplitData.node0332 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0333
  · rfl
  · rfl

def B0331 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0332, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M7300_7500.SplitData.node0331 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0332
  · rfl

def B0330 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0331, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M7300_7500.SplitData.node0330 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0331
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0323 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0324, (.leaf 5 (Common.fact 308).pointIds 308), B0330]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M7300_7500.SplitData.node0323 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · exact treeEq0330

theorem accepted0323 : B0323.accepted = true := by decide +kernel
theorem checked0323 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0323 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0323]
  exact B0323.sound accepted0323
#print axioms checked0323

def Tip0321_0323 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0323 ![2535301200456458802993406411137, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0323
def B0342 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M7300_7500.SplitData.node0342 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0341 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0342, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M7300_7500.SplitData.node0341 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl

def B0340 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0341]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M7300_7500.SplitData.node0340 := by
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
  · exact treeEq0341

def B0339 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B0340, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M7300_7500.SplitData.node0339 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0340
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0338 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0339]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M7300_7500.SplitData.node0338 := by
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
  · exact treeEq0339

def B0337 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B0338, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M7300_7500.SplitData.node0337 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0338
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0336 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 655).pointIds 655), B0337, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M7300_7500.SplitData.node0336 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl

def B0335 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0336, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M7300_7500.SplitData.node0335 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336
  · rfl
  · rfl

def B0322 : Block := .branch 101 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0321_0323, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0335]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M7300_7500.SplitData.node0322 := by
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
  · exact treeEq0335

def B0350 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M7300_7500.SplitData.node0350 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0349 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0350, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M7300_7500.SplitData.node0349 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0350
  · rfl
  · rfl

def B0348 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0349]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M7300_7500.SplitData.node0348 := by
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
  · exact treeEq0349

def B0347 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B0348, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M7300_7500.SplitData.node0347 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0348
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0346 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0347]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M7300_7500.SplitData.node0346 := by
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
  · exact treeEq0347

def B0345 : Block := .branch 169 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B0346, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M7300_7500.SplitData.node0345 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0346
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0344 : Block := .branch 170 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 655).pointIds 655), B0345, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M7300_7500.SplitData.node0344 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl

def B0343 : Block := .branch 171 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0344, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M7300_7500.SplitData.node0343 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl
  · rfl

def B0321 : Block := .branch 91 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0322, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0343]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M7300_7500.SplitData.node0321 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0322
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0343

theorem accepted0321 : B0321.accepted = true := by decide +kernel
theorem checked0321 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0321 (maskNeeds ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0321]
  exact B0321.sound accepted0321
#print axioms checked0321

end HexagonCover.NBand.M7300_7500.SplitTree.Run0003
