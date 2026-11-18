import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0018
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0019
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip1374_1376 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1376 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0018.checked1376
def B1413 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq1413 : B1413.tree = HexagonCover.NBand.M7300_7500.SplitData.node1413 := by
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

def B1412 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1413, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1412 : B1412.tree = HexagonCover.NBand.M7300_7500.SplitData.node1412 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1413
  · rfl
  · rfl

def B1411 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1412]
theorem treeEq1411 : B1411.tree = HexagonCover.NBand.M7300_7500.SplitData.node1411 := by
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
  · exact treeEq1412

def B1410 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B1411, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1410 : B1410.tree = HexagonCover.NBand.M7300_7500.SplitData.node1410 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1411
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1409 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1410]
theorem treeEq1409 : B1409.tree = HexagonCover.NBand.M7300_7500.SplitData.node1409 := by
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
  · exact treeEq1410

def B1408 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B1409, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1408 : B1408.tree = HexagonCover.NBand.M7300_7500.SplitData.node1408 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1409
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1407 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1408, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1407 : B1407.tree = HexagonCover.NBand.M7300_7500.SplitData.node1407 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1408
  · rfl

def B1406 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1407, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq1406 : B1406.tree = HexagonCover.NBand.M7300_7500.SplitData.node1406 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1407
  · rfl
  · rfl

def B1375 : Block := .branch 89 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip1374_1376, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1406]
theorem treeEq1375 : B1375.tree = HexagonCover.NBand.M7300_7500.SplitData.node1375 := by
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
  · exact treeEq1406

def B1421 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq1421 : B1421.tree = HexagonCover.NBand.M7300_7500.SplitData.node1421 := by
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

def B1420 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1421, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq1420 : B1420.tree = HexagonCover.NBand.M7300_7500.SplitData.node1420 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1421
  · rfl
  · rfl

def B1419 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1420]
theorem treeEq1419 : B1419.tree = HexagonCover.NBand.M7300_7500.SplitData.node1419 := by
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
  · exact treeEq1420

def B1418 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B1419, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1418 : B1418.tree = HexagonCover.NBand.M7300_7500.SplitData.node1418 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1419
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1417 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1418]
theorem treeEq1417 : B1417.tree = HexagonCover.NBand.M7300_7500.SplitData.node1417 := by
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
  · exact treeEq1418

def B1416 : Block := .branch 169 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B1417, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1416 : B1416.tree = HexagonCover.NBand.M7300_7500.SplitData.node1416 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1417
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1415 : Block := .branch 170 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1416, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1415 : B1415.tree = HexagonCover.NBand.M7300_7500.SplitData.node1415 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1416
  · rfl

def B1414 : Block := .branch 171 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1415, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq1414 : B1414.tree = HexagonCover.NBand.M7300_7500.SplitData.node1414 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1415
  · rfl
  · rfl

def B1374 : Block := .branch 86 ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B1375, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B1414]
theorem treeEq1374 : B1374.tree = HexagonCover.NBand.M7300_7500.SplitData.node1374 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1375
  · rfl
  · rfl
  · exact treeEq1414

theorem accepted1374 : B1374.accepted = true := by decide +kernel
theorem checked1374 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1374 (maskNeeds ![385, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1374]
  exact B1374.sound accepted1374
#print axioms checked1374

def B1455 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1455 : B1455.tree = HexagonCover.NBand.M7300_7500.SplitData.node1455 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1454 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1455]
theorem treeEq1454 : B1454.tree = HexagonCover.NBand.M7300_7500.SplitData.node1454 := by
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
  · exact treeEq1455

def B1453 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1454]
theorem treeEq1453 : B1453.tree = HexagonCover.NBand.M7300_7500.SplitData.node1453 := by
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
  · exact treeEq1454

def B1452 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1453, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1452 : B1452.tree = HexagonCover.NBand.M7300_7500.SplitData.node1452 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1453
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1451 : Block := .branch 170 ![2535301200456458802993406411137, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846353304459082801411451530724212047888, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 679).pointIds 679), B1452, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1451 : B1451.tree = HexagonCover.NBand.M7300_7500.SplitData.node1451 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1452
  · rfl

def B1460 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1460 : B1460.tree = HexagonCover.NBand.M7300_7500.SplitData.node1460 := by
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

def B1459 : Block := .branch 171 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1460]
theorem treeEq1459 : B1459.tree = HexagonCover.NBand.M7300_7500.SplitData.node1459 := by
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
  · exact treeEq1460

def B1458 : Block := .branch 170 ![385, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 42535295865117307932921825928971419680, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), B1459, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1458 : B1458.tree = HexagonCover.NBand.M7300_7500.SplitData.node1458 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1459
  · rfl
  · rfl

def B1457 : Block := .branch 125 ![374144419156711157447272335445480168895904795853185, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 98320, 393248, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B1458, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1457 : B1457.tree = HexagonCover.NBand.M7300_7500.SplitData.node1457 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1458
  · rfl

def B1456 : Block := .branch 168 ![10387129018270111715863986064851329, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071807775992273212354753230527791168] ![B1457, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1456 : B1456.tree = HexagonCover.NBand.M7300_7500.SplitData.node1456 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1457
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1450 : Block := .branch 108 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B1451, (.leaf 5 (Common.fact 308).pointIds 308), B1456]
theorem treeEq1450 : B1450.tree = HexagonCover.NBand.M7300_7500.SplitData.node1450 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1451
  · rfl
  · exact treeEq1456

theorem accepted1450 : B1450.accepted = true := by decide +kernel
theorem checked1450 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1450 (maskNeeds ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1450]
  exact B1450.sound accepted1450
#print axioms checked1450

def Tip1448_1450 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1450 ![10387129018270111715863986064851329, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1450
def B1469 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1469 : B1469.tree = HexagonCover.NBand.M7300_7500.SplitData.node1469 := by
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

def B1468 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B1469, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq1468 : B1468.tree = HexagonCover.NBand.M7300_7500.SplitData.node1468 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1469
  · rfl
  · rfl

def B1467 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B1468, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1467 : B1467.tree = HexagonCover.NBand.M7300_7500.SplitData.node1467 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1468
  · rfl

def B1466 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1467]
theorem treeEq1466 : B1466.tree = HexagonCover.NBand.M7300_7500.SplitData.node1466 := by
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
  · exact treeEq1467

def B1465 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B1466, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1465 : B1465.tree = HexagonCover.NBand.M7300_7500.SplitData.node1465 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1466
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1464 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1465]
theorem treeEq1464 : B1464.tree = HexagonCover.NBand.M7300_7500.SplitData.node1464 := by
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
  · exact treeEq1465

def B1463 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739815242086773067913625664] ![B1464, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1463 : B1463.tree = HexagonCover.NBand.M7300_7500.SplitData.node1463 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1464
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1462 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1463, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1462 : B1462.tree = HexagonCover.NBand.M7300_7500.SplitData.node1462 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1463
  · rfl

def B1461 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1462, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1461 : B1461.tree = HexagonCover.NBand.M7300_7500.SplitData.node1461 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1462
  · rfl
  · rfl

def B1449 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip1448_1450, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1461]
theorem treeEq1449 : B1449.tree = HexagonCover.NBand.M7300_7500.SplitData.node1449 := by
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
  · exact treeEq1461

def B1477 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1477 : B1477.tree = HexagonCover.NBand.M7300_7500.SplitData.node1477 := by
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

def B1476 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1477, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1476 : B1476.tree = HexagonCover.NBand.M7300_7500.SplitData.node1476 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1477
  · rfl
  · rfl

def B1475 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1476]
theorem treeEq1475 : B1475.tree = HexagonCover.NBand.M7300_7500.SplitData.node1475 := by
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
  · exact treeEq1476

def B1474 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B1475, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1474 : B1474.tree = HexagonCover.NBand.M7300_7500.SplitData.node1474 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1475
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1473 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1474]
theorem treeEq1473 : B1473.tree = HexagonCover.NBand.M7300_7500.SplitData.node1473 := by
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
  · exact treeEq1474

def B1472 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1473, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1472 : B1472.tree = HexagonCover.NBand.M7300_7500.SplitData.node1472 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1473
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1471 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1472, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1471 : B1471.tree = HexagonCover.NBand.M7300_7500.SplitData.node1471 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1472
  · rfl

def B1470 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1471, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1470 : B1470.tree = HexagonCover.NBand.M7300_7500.SplitData.node1470 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1471
  · rfl
  · rfl

def B1448 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 86).pointIds 86), B1449, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1470]
theorem treeEq1448 : B1448.tree = HexagonCover.NBand.M7300_7500.SplitData.node1448 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1449
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1470

theorem accepted1448 : B1448.accepted = true := by decide +kernel
theorem checked1448 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1448 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1448]
  exact B1448.sound accepted1448
#print axioms checked1448

def Tip1446_1448 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1448 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1448
def B1484 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1484 : B1484.tree = HexagonCover.NBand.M7300_7500.SplitData.node1484 := by
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

def B1483 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 24114777037737969633617851498342021113061488197696] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1484, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq1483 : B1483.tree = HexagonCover.NBand.M7300_7500.SplitData.node1483 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1484
  · rfl
  · rfl

def B1482 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 23384026219072518174516009081983879603233521926208] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1483]
theorem treeEq1482 : B1482.tree = HexagonCover.NBand.M7300_7500.SplitData.node1482 := by
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
  · exact treeEq1483

def B1481 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737941821641931621890, 6148, 24584, 98320, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1482]
theorem treeEq1481 : B1481.tree = HexagonCover.NBand.M7300_7500.SplitData.node1481 := by
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
  · exact treeEq1482

def B1480 : Block := .branch 169 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515986038083306341688410176] ![B1481, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1480 : B1480.tree = HexagonCover.NBand.M7300_7500.SplitData.node1480 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1481
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1479 : Block := .branch 170 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1480, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1479 : B1479.tree = HexagonCover.NBand.M7300_7500.SplitData.node1479 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1480
  · rfl

def B1478 : Block := .branch 171 ![2475880078570760549798248833, 737941821641931621890, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1479, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1478 : B1478.tree = HexagonCover.NBand.M7300_7500.SplitData.node1478 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1479
  · rfl
  · rfl

def B1447 : Block := .branch 86 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), Tip1446_1448, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B1478]
theorem treeEq1447 : B1447.tree = HexagonCover.NBand.M7300_7500.SplitData.node1447 := by
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
  · exact treeEq1478

def B1492 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq1492 : B1492.tree = HexagonCover.NBand.M7300_7500.SplitData.node1492 := by
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

def B1491 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659249188331332202542365409344] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1492, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq1491 : B1491.tree = HexagonCover.NBand.M7300_7500.SplitData.node1491 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1492
  · rfl
  · rfl

def B1490 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515932012962879170623634407488] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1491]
theorem treeEq1490 : B1490.tree = HexagonCover.NBand.M7300_7500.SplitData.node1490 := by
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
  · exact treeEq1491

def B1489 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241497972700515692359188544] ![B1490, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1489 : B1489.tree = HexagonCover.NBand.M7300_7500.SplitData.node1489 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1490
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1488 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257284174512172201197438500928] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1489]
theorem treeEq1488 : B1488.tree = HexagonCover.NBand.M7300_7500.SplitData.node1488 := by
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
  · exact treeEq1489

def B1487 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438917017082873731800891456] ![B1488, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 777).pointIds 777), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1487 : B1487.tree = HexagonCover.NBand.M7300_7500.SplitData.node1487 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1486 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 775).pointIds 775), (.leaf 3 (Common.fact 776).pointIds 776), (.leaf 4 (Common.fact 655).pointIds 655), B1487, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1486 : B1486.tree = HexagonCover.NBand.M7300_7500.SplitData.node1486 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1487
  · rfl

def B1485 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438917017082873731800891456] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 780).pointIds 780), B1486, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq1485 : B1485.tree = HexagonCover.NBand.M7300_7500.SplitData.node1485 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1486
  · rfl
  · rfl

def B1446 : Block := .branch 78 ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 134).pointIds 134), B1447, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B1485]
theorem treeEq1446 : B1446.tree = HexagonCover.NBand.M7300_7500.SplitData.node1446 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1447
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1485

theorem accepted1446 : B1446.accepted = true := by decide +kernel
theorem checked1446 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1446 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 55376261018147624964, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1446]
  exact B1446.sound accepted1446
#print axioms checked1446

end HexagonCover.NBand.M7300_7500.SplitTree.Run0019
