import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0007
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0449_0451 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0451 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0006.checked0451
def B0506 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M7300_7500.SplitData.node0506 := by
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

def B0505 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0506, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M7300_7500.SplitData.node0505 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0506
  · rfl
  · rfl

def B0504 : Block := .branch 125 ![385, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0505, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M7300_7500.SplitData.node0504 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0505
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0503 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 753).pointIds 753), B0504, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M7300_7500.SplitData.node0503 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0504
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0502 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0503]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M7300_7500.SplitData.node0502 := by
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
  · exact treeEq0503

def B0501 : Block := .branch 169 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0502, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M7300_7500.SplitData.node0501 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0502
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0500 : Block := .branch 170 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0501, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M7300_7500.SplitData.node0500 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl

def B0499 : Block := .branch 171 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0500, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M7300_7500.SplitData.node0499 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0500
  · rfl
  · rfl

def B0450 : Block := .branch 80 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0449_0451, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B0499]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M7300_7500.SplitData.node0450 := by
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
  · exact treeEq0499

def B0514 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M7300_7500.SplitData.node0514 := by
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

def B0513 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0514, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M7300_7500.SplitData.node0513 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0514
  · rfl
  · rfl

def B0512 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0513]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M7300_7500.SplitData.node0512 := by
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
  · exact treeEq0513

def B0511 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B0512, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M7300_7500.SplitData.node0511 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0512
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0510 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0511]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M7300_7500.SplitData.node0510 := by
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
  · exact treeEq0511

def B0509 : Block := .branch 169 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B0510, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M7300_7500.SplitData.node0509 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0510
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0508 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0509, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M7300_7500.SplitData.node0508 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0509
  · rfl

def B0507 : Block := .branch 171 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0508, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M7300_7500.SplitData.node0507 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0508
  · rfl
  · rfl

def B0449 : Block := .branch 78 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B0450, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0507]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M7300_7500.SplitData.node0449 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0450
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0507

theorem accepted0449 : B0449.accepted = true := by decide +kernel
theorem checked0449 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0449 (maskNeeds ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0449]
  exact B0449.sound accepted0449
#print axioms checked0449

def B0592 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M7300_7500.SplitData.node0592 := by
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

def B0591 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0592]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M7300_7500.SplitData.node0591 := by
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
  · exact treeEq0592

def B0590 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0591, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M7300_7500.SplitData.node0590 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0591
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0589 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0590]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M7300_7500.SplitData.node0589 := by
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
  · exact treeEq0590

def B0588 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B0589, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M7300_7500.SplitData.node0588 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0589
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0587 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 679).pointIds 679), B0588, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M7300_7500.SplitData.node0587 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0588
  · rfl

def B0597 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M7300_7500.SplitData.node0597 := by
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

def B0596 : Block := .branch 171 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0597]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M7300_7500.SplitData.node0596 := by
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
  · exact treeEq0597

def B0595 : Block := .branch 170 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), B0596, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M7300_7500.SplitData.node0595 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0596
  · rfl
  · rfl

def B0594 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0595, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M7300_7500.SplitData.node0594 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0595
  · rfl

def B0593 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0594, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M7300_7500.SplitData.node0593 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0594
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0586 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0587, (.leaf 5 (Common.fact 308).pointIds 308), B0593]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M7300_7500.SplitData.node0586 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0587
  · rfl
  · exact treeEq0593

theorem accepted0586 : B0586.accepted = true := by decide +kernel
theorem checked0586 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0586 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0586]
  exact B0586.sound accepted0586
#print axioms checked0586

def Tip0584_0586 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0586 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0586
def B0605 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M7300_7500.SplitData.node0605 := by
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

def B0604 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0605, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M7300_7500.SplitData.node0604 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0605
  · rfl
  · rfl

def B0603 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0604]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M7300_7500.SplitData.node0603 := by
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
  · exact treeEq0604

def B0602 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B0603, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M7300_7500.SplitData.node0602 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0603
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0601 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0602]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M7300_7500.SplitData.node0601 := by
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
  · exact treeEq0602

def B0600 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B0601, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M7300_7500.SplitData.node0600 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0601
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0599 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0600, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M7300_7500.SplitData.node0599 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0600
  · rfl

def B0598 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0599, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M7300_7500.SplitData.node0598 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0599
  · rfl
  · rfl

def B0585 : Block := .branch 101 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0584_0586, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0598]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M7300_7500.SplitData.node0585 := by
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
  · exact treeEq0598

def B0613 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M7300_7500.SplitData.node0613 := by
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

def B0612 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0613, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M7300_7500.SplitData.node0612 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0613
  · rfl
  · rfl

def B0611 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0612]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M7300_7500.SplitData.node0611 := by
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
  · exact treeEq0612

def B0610 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B0611, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M7300_7500.SplitData.node0610 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0611
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0609 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0610]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M7300_7500.SplitData.node0609 := by
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
  · exact treeEq0610

def B0608 : Block := .branch 169 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B0609, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M7300_7500.SplitData.node0608 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0609
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0607 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0608, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M7300_7500.SplitData.node0607 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl

def B0606 : Block := .branch 171 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0607, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M7300_7500.SplitData.node0606 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0607
  · rfl
  · rfl

def B0584 : Block := .branch 91 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0585, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0606]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M7300_7500.SplitData.node0584 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0585
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0606

theorem accepted0584 : B0584.accepted = true := by decide +kernel
theorem checked0584 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0584 (maskNeeds ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0584]
  exact B0584.sound accepted0584
#print axioms checked0584

def Tip0582_0584 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0584 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0584
def B0621 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M7300_7500.SplitData.node0621 := by
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

def B0620 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0621, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M7300_7500.SplitData.node0620 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl
  · rfl

def B0619 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0620]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M7300_7500.SplitData.node0619 := by
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
  · exact treeEq0620

def B0618 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0619, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M7300_7500.SplitData.node0618 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0619
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0617 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0618]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M7300_7500.SplitData.node0617 := by
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
  · exact treeEq0618

def B0616 : Block := .branch 169 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B0617, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M7300_7500.SplitData.node0616 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0617
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0615 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0616, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M7300_7500.SplitData.node0615 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0616
  · rfl

def B0614 : Block := .branch 171 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0615, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M7300_7500.SplitData.node0614 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0615
  · rfl
  · rfl

def B0583 : Block := .branch 89 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip0582_0584, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B0614]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M7300_7500.SplitData.node0583 := by
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
  · exact treeEq0614

def B0629 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M7300_7500.SplitData.node0629 := by
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

def B0628 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0629, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M7300_7500.SplitData.node0628 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0629
  · rfl
  · rfl

def B0627 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0628]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M7300_7500.SplitData.node0627 := by
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
  · exact treeEq0628

def B0626 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B0627, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M7300_7500.SplitData.node0626 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0627
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0625 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0626]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M7300_7500.SplitData.node0625 := by
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
  · exact treeEq0626

def B0624 : Block := .branch 169 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B0625, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M7300_7500.SplitData.node0624 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0623 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0624, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M7300_7500.SplitData.node0623 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0624
  · rfl

def B0622 : Block := .branch 171 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0623, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M7300_7500.SplitData.node0622 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0623
  · rfl
  · rfl

def B0582 : Block := .branch 86 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0583, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0622]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M7300_7500.SplitData.node0582 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0583
  · rfl
  · rfl
  · exact treeEq0622

theorem accepted0582 : B0582.accepted = true := by decide +kernel
theorem checked0582 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0582 (maskNeeds ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0582]
  exact B0582.sound accepted0582
#print axioms checked0582

def B0663 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M7300_7500.SplitData.node0663 := by
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

def B0662 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0663]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M7300_7500.SplitData.node0662 := by
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
  · exact treeEq0663

def B0661 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0662]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M7300_7500.SplitData.node0661 := by
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
  · exact treeEq0662

def B0660 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 7120443212451886929924, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B0661, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M7300_7500.SplitData.node0660 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0661
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0659 : Block := .branch 170 ![2535301200456458802993406411137, 737941821641931621890, 7120443212451886929924, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 679).pointIds 679), B0660, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M7300_7500.SplitData.node0659 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0660
  · rfl

def B0668 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M7300_7500.SplitData.node0668 := by
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

def B0667 : Block := .branch 171 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0668]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M7300_7500.SplitData.node0667 := by
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
  · exact treeEq0668

def B0666 : Block := .branch 170 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), B0667, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M7300_7500.SplitData.node0666 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0667
  · rfl
  · rfl

def B0665 : Block := .branch 125 ![374144419156711157447272335445480168895904795853185, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0666, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M7300_7500.SplitData.node0665 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0666
  · rfl

def B0664 : Block := .branch 168 ![10387129018270111715863986064851329, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071807775992273212354753230527791168] ![B0665, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M7300_7500.SplitData.node0664 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0658 : Block := .branch 108 ![10387129018270111715863986064851329, 738230052018083333634, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0659, (.leaf 5 (Common.fact 308).pointIds 308), B0664]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M7300_7500.SplitData.node0658 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · rfl
  · exact treeEq0664

theorem accepted0658 : B0658.accepted = true := by decide +kernel
theorem checked0658 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0658 (maskNeeds ![10387129018270111715863986064851329, 738230052018083333634, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq0658]
  exact B0658.sound accepted0658
#print axioms checked0658

end HexagonCover.NBand.M7300_7500.SplitTree.Run0007
