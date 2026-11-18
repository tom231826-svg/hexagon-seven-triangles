import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0035
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0036
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2517_2519 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2519 ![385, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0035.checked2519
def B2559 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq2559 : B2559.tree = HexagonCover.NBand.M7300_7500.SplitData.node2559 := by
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

def B2558 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2559, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq2558 : B2558.tree = HexagonCover.NBand.M7300_7500.SplitData.node2558 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2559
  · rfl
  · rfl

def B2557 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2558]
theorem treeEq2557 : B2557.tree = HexagonCover.NBand.M7300_7500.SplitData.node2557 := by
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
  · exact treeEq2558

def B2556 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2557, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2556 : B2556.tree = HexagonCover.NBand.M7300_7500.SplitData.node2556 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2557
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2555 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2556]
theorem treeEq2555 : B2555.tree = HexagonCover.NBand.M7300_7500.SplitData.node2555 := by
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
  · exact treeEq2556

def B2554 : Block := .branch 169 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2555, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2554 : B2554.tree = HexagonCover.NBand.M7300_7500.SplitData.node2554 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2555
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2553 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2554, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2553 : B2553.tree = HexagonCover.NBand.M7300_7500.SplitData.node2553 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2554
  · rfl

def B2552 : Block := .branch 171 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2553, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq2552 : B2552.tree = HexagonCover.NBand.M7300_7500.SplitData.node2552 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2553
  · rfl
  · rfl

def B2518 : Block := .branch 89 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip2517_2519, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2552]
theorem treeEq2518 : B2518.tree = HexagonCover.NBand.M7300_7500.SplitData.node2518 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2552

def B2567 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq2567 : B2567.tree = HexagonCover.NBand.M7300_7500.SplitData.node2567 := by
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

def B2566 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2567, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq2566 : B2566.tree = HexagonCover.NBand.M7300_7500.SplitData.node2566 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2567
  · rfl
  · rfl

def B2565 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2566]
theorem treeEq2565 : B2565.tree = HexagonCover.NBand.M7300_7500.SplitData.node2565 := by
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
  · exact treeEq2566

def B2564 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B2565, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2564 : B2564.tree = HexagonCover.NBand.M7300_7500.SplitData.node2564 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2565
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2563 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2564]
theorem treeEq2563 : B2563.tree = HexagonCover.NBand.M7300_7500.SplitData.node2563 := by
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
  · exact treeEq2564

def B2562 : Block := .branch 169 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B2563, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2562 : B2562.tree = HexagonCover.NBand.M7300_7500.SplitData.node2562 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2563
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2561 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2562, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2561 : B2561.tree = HexagonCover.NBand.M7300_7500.SplitData.node2561 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2562
  · rfl

def B2560 : Block := .branch 171 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2561, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq2560 : B2560.tree = HexagonCover.NBand.M7300_7500.SplitData.node2560 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2561
  · rfl
  · rfl

def B2517 : Block := .branch 86 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 856).pointIds 856), B2518, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2560]
theorem treeEq2517 : B2517.tree = HexagonCover.NBand.M7300_7500.SplitData.node2517 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2518
  · rfl
  · rfl
  · exact treeEq2560

theorem accepted2517 : B2517.accepted = true := by decide +kernel
theorem checked2517 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2517 (maskNeeds ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2517]
  exact B2517.sound accepted2517
#print axioms checked2517

def B2598 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq2598 : B2598.tree = HexagonCover.NBand.M7300_7500.SplitData.node2598 := by
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

def B2597 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2598]
theorem treeEq2597 : B2597.tree = HexagonCover.NBand.M7300_7500.SplitData.node2597 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2598

def B2596 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430925934796998146, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B2597, (.leaf 1 (Common.fact 823).pointIds 823), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq2596 : B2596.tree = HexagonCover.NBand.M7300_7500.SplitData.node2596 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2597
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2595 : Block := .branch 160 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B2596, (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2595 : B2595.tree = HexagonCover.NBand.M7300_7500.SplitData.node2595 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2596
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2594 : Block := .branch 75 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B2595, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2594 : B2594.tree = HexagonCover.NBand.M7300_7500.SplitData.node2594 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2595
  · rfl
  · rfl
  · rfl
  · rfl

def B2593 : Block := .branch 162 ![10384593717069655257060992658440577, 295147906278864455170, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2594, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq2593 : B2593.tree = HexagonCover.NBand.M7300_7500.SplitData.node2593 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2594
  · rfl
  · rfl
  · rfl

def B2592 : Block := .branch 168 ![10384593717069655257060992658440577, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 2993155353275467247964403511790218520207821268058176] ![B2593, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2592 : B2592.tree = HexagonCover.NBand.M7300_7500.SplitData.node2592 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2593
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2591 : Block := .branch 171 ![10384593717069655257060992658440577, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2592]
theorem treeEq2591 : B2591.tree = HexagonCover.NBand.M7300_7500.SplitData.node2591 := by
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
  · exact treeEq2592

def B2590 : Block := .branch 170 ![10384593717069655257060992658440577, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2591, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2590 : B2590.tree = HexagonCover.NBand.M7300_7500.SplitData.node2590 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2591
  · rfl
  · rfl

def B2589 : Block := .branch 169 ![10384593717070245552871351364092289, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2590, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2589 : B2589.tree = HexagonCover.NBand.M7300_7500.SplitData.node2589 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2590
  · rfl

theorem accepted2589 : B2589.accepted = true := by decide +kernel
theorem checked2589 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2589 (maskNeeds ![10384593717070245552871351364092289, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2589]
  exact B2589.sound accepted2589
#print axioms checked2589

def Tip2588_2589 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2589 ![10384593717070245552871351364092289, 295364079060978238978, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2589
def B2608 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq2608 : B2608.tree = HexagonCover.NBand.M7300_7500.SplitData.node2608 := by
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

def B2607 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2608, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq2607 : B2607.tree = HexagonCover.NBand.M7300_7500.SplitData.node2607 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2608
  · rfl
  · rfl

def B2606 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2607]
theorem treeEq2606 : B2606.tree = HexagonCover.NBand.M7300_7500.SplitData.node2606 := by
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
  · exact treeEq2607

def B2605 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B2606, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2605 : B2605.tree = HexagonCover.NBand.M7300_7500.SplitData.node2605 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2606
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2604 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2605]
theorem treeEq2604 : B2604.tree = HexagonCover.NBand.M7300_7500.SplitData.node2604 := by
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
  · exact treeEq2605

def B2603 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2604]
theorem treeEq2603 : B2603.tree = HexagonCover.NBand.M7300_7500.SplitData.node2603 := by
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
  · exact treeEq2604

def B2602 : Block := .branch 169 ![2475880078570760549798248833, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B2603, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2602 : B2602.tree = HexagonCover.NBand.M7300_7500.SplitData.node2602 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2603
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2601 : Block := .branch 170 ![2475880078570760549798248833, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2602, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2601 : B2601.tree = HexagonCover.NBand.M7300_7500.SplitData.node2601 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2602
  · rfl

def B2600 : Block := .branch 171 ![2475880078570760549798248833, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2601, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq2600 : B2600.tree = HexagonCover.NBand.M7300_7500.SplitData.node2600 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2601
  · rfl
  · rfl

def B2599 : Block := .branch 160 ![2475880078570760549798248833, 738085936830007477762, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 689).pointIds 689), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2600]
theorem treeEq2599 : B2599.tree = HexagonCover.NBand.M7300_7500.SplitData.node2599 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2600

def B2588 : Block := .branch 69 ![10384596192949733827821542456689025, 442938031650654651906, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip2588_2589, B2599, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2588 : B2588.tree = HexagonCover.NBand.M7300_7500.SplitData.node2588 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2599
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2588 : B2588.accepted = true := by decide +kernel
theorem checked2588 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2588 (maskNeeds ![10384596192949733827821542456689025, 442938031650654651906, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq2588]
  exact B2588.sound accepted2588
#print axioms checked2588

def Tip2515_2517 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2517 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2517
def B2576 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq2576 : B2576.tree = HexagonCover.NBand.M7300_7500.SplitData.node2576 := by
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

def B2575 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B2576, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq2575 : B2575.tree = HexagonCover.NBand.M7300_7500.SplitData.node2575 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2576
  · rfl
  · rfl

def B2574 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B2575, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq2574 : B2574.tree = HexagonCover.NBand.M7300_7500.SplitData.node2574 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2575
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2573 : Block := .branch 160 ![385, 302821822772709548885506, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 860).pointIds 860), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2574]
theorem treeEq2573 : B2573.tree = HexagonCover.NBand.M7300_7500.SplitData.node2573 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2574

def B2572 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231526962350843233794, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B2573, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq2572 : B2572.tree = HexagonCover.NBand.M7300_7500.SplitData.node2572 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2573
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2571 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231526962350843233794, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2572]
theorem treeEq2571 : B2571.tree = HexagonCover.NBand.M7300_7500.SplitData.node2571 := by
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
  · exact treeEq2572

def B2570 : Block := .branch 169 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B2571, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2570 : B2570.tree = HexagonCover.NBand.M7300_7500.SplitData.node2570 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2571
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2569 : Block := .branch 170 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2570, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2569 : B2569.tree = HexagonCover.NBand.M7300_7500.SplitData.node2569 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2570
  · rfl

def B2568 : Block := .branch 171 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2569, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq2568 : B2568.tree = HexagonCover.NBand.M7300_7500.SplitData.node2568 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2569
  · rfl
  · rfl

def B2516 : Block := .branch 80 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2515_2517, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B2568]
theorem treeEq2516 : B2516.tree = HexagonCover.NBand.M7300_7500.SplitData.node2516 := by
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
  · exact treeEq2568

def B2584 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2584 : B2584.tree = HexagonCover.NBand.M7300_7500.SplitData.node2584 := by
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

def B2583 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2584, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2583 : B2583.tree = HexagonCover.NBand.M7300_7500.SplitData.node2583 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2584
  · rfl
  · rfl

def B2582 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2583]
theorem treeEq2582 : B2582.tree = HexagonCover.NBand.M7300_7500.SplitData.node2582 := by
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
  · exact treeEq2583

def B2581 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B2582, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2581 : B2581.tree = HexagonCover.NBand.M7300_7500.SplitData.node2581 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2582
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2580 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2581]
theorem treeEq2580 : B2580.tree = HexagonCover.NBand.M7300_7500.SplitData.node2580 := by
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
  · exact treeEq2581

def B2579 : Block := .branch 169 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B2580, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2579 : B2579.tree = HexagonCover.NBand.M7300_7500.SplitData.node2579 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2580
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2578 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2579, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2578 : B2578.tree = HexagonCover.NBand.M7300_7500.SplitData.node2578 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2579
  · rfl

def B2577 : Block := .branch 171 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2578, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq2577 : B2577.tree = HexagonCover.NBand.M7300_7500.SplitData.node2577 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2578
  · rfl
  · rfl

def B2515 : Block := .branch 78 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B2516, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B2577]
theorem treeEq2515 : B2515.tree = HexagonCover.NBand.M7300_7500.SplitData.node2515 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2516
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2577

theorem accepted2515 : B2515.accepted = true := by decide +kernel
theorem checked2515 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2515 (maskNeeds ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2515]
  exact B2515.sound accepted2515
#print axioms checked2515

def Tip2514_2588 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2588 ![10384596192949733827821542456689025, 442938031650654651906, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked2588
def Tip2514_2515 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2515 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2515
def B2617 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5316911983139663491615228241121476624, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 725).pointIds 725), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq2617 : B2617.tree = HexagonCover.NBand.M7300_7500.SplitData.node2617 := by
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

def B2616 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), B2617, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq2616 : B2616.tree = HexagonCover.NBand.M7300_7500.SplitData.node2616 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2617
  · rfl
  · rfl

def B2615 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2616]
theorem treeEq2615 : B2615.tree = HexagonCover.NBand.M7300_7500.SplitData.node2615 := by
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
  · exact treeEq2616

def B2614 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B2615, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2614 : B2614.tree = HexagonCover.NBand.M7300_7500.SplitData.node2614 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2615
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2613 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B2614, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2613 : B2613.tree = HexagonCover.NBand.M7300_7500.SplitData.node2613 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2614
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2612 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2613]
theorem treeEq2612 : B2612.tree = HexagonCover.NBand.M7300_7500.SplitData.node2612 := by
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
  · exact treeEq2613

def B2611 : Block := .branch 169 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B2612, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2611 : B2611.tree = HexagonCover.NBand.M7300_7500.SplitData.node2611 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2612
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2610 : Block := .branch 170 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2611, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2610 : B2610.tree = HexagonCover.NBand.M7300_7500.SplitData.node2610 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2611
  · rfl

def B2609 : Block := .branch 171 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2610, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq2609 : B2609.tree = HexagonCover.NBand.M7300_7500.SplitData.node2609 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2610
  · rfl
  · rfl

def B2587 : Block := .branch 68 ![10384596192949733827821542456689025, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2514_2588, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B2609]
theorem treeEq2587 : B2587.tree = HexagonCover.NBand.M7300_7500.SplitData.node2587 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2609

def B2586 : Block := .branch 91 ![10384593717069655257060992658440577, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2587, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2586 : B2586.tree = HexagonCover.NBand.M7300_7500.SplitData.node2586 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2587
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2585 : Block := .branch 113 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2586, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2585 : B2585.tree = HexagonCover.NBand.M7300_7500.SplitData.node2585 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2586
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2514 : Block := .branch 76 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip2514_2515, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B2585]
theorem treeEq2514 : B2514.tree = HexagonCover.NBand.M7300_7500.SplitData.node2514 := by
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
  · exact treeEq2585

theorem accepted2514 : B2514.accepted = true := by decide +kernel
theorem checked2514 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2514 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2514]
  exact B2514.sound accepted2514
#print axioms checked2514

end HexagonCover.NBand.M7300_7500.SplitTree.Run0036
