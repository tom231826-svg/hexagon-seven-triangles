import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0317_0319 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0319 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0004.checked0319
def B0374 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M7300_7500.SplitData.node0374 := by
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

def B0373 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0374, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M7300_7500.SplitData.node0373 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0374
  · rfl
  · rfl

def B0372 : Block := .branch 125 ![385, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0373, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M7300_7500.SplitData.node0372 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0373
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0371 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 753).pointIds 753), B0372, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M7300_7500.SplitData.node0371 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0372
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0370 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0371]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M7300_7500.SplitData.node0370 := by
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
  · exact treeEq0371

def B0369 : Block := .branch 169 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B0370, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M7300_7500.SplitData.node0369 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0370
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0368 : Block := .branch 170 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 655).pointIds 655), B0369, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M7300_7500.SplitData.node0368 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0369
  · rfl

def B0367 : Block := .branch 171 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0368, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M7300_7500.SplitData.node0367 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0368
  · rfl
  · rfl

def B0318 : Block := .branch 80 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0317_0319, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B0367]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M7300_7500.SplitData.node0318 := by
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
  · exact treeEq0367

def B0382 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M7300_7500.SplitData.node0382 := by
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

def B0381 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0382, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M7300_7500.SplitData.node0381 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl
  · rfl

def B0380 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0381]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M7300_7500.SplitData.node0380 := by
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
  · exact treeEq0381

def B0379 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B0380, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M7300_7500.SplitData.node0379 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0380
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0378 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0379]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M7300_7500.SplitData.node0378 := by
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
  · exact treeEq0379

def B0377 : Block := .branch 169 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B0378, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M7300_7500.SplitData.node0377 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0378
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0376 : Block := .branch 170 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 655).pointIds 655), B0377, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M7300_7500.SplitData.node0376 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl

def B0375 : Block := .branch 171 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0376, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M7300_7500.SplitData.node0375 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0376
  · rfl
  · rfl

def B0317 : Block := .branch 78 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B0318, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0375]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M7300_7500.SplitData.node0317 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0318
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375

theorem accepted0317 : B0317.accepted = true := by decide +kernel
theorem checked0317 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0317 (maskNeeds ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0317]
  exact B0317.sound accepted0317
#print axioms checked0317

def Tip0316_0391 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0391 ![10384596192949733827821542456689025, 738230052018083333634, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0004.checked0391
def Tip0316_0317 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0317 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0317
def B0390 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M7300_7500.SplitData.node0390 := by
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

def B0389 : Block := .branch 171 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0390]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M7300_7500.SplitData.node0389 := by
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
  · exact treeEq0390

def B0388 : Block := .branch 170 ![385, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), B0389, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M7300_7500.SplitData.node0388 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl
  · rfl

def B0387 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), B0388, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M7300_7500.SplitData.node0387 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388
  · rfl

def B0386 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0387, Tip0316_0391, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M7300_7500.SplitData.node0386 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0387
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0446 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M7300_7500.SplitData.node0446 := by
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

def B0445 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), B0446, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M7300_7500.SplitData.node0445 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0446
  · rfl
  · rfl

def B0444 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0445]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M7300_7500.SplitData.node0444 := by
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
  · exact treeEq0445

def B0443 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B0444, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M7300_7500.SplitData.node0443 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0444
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0442 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B0443, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M7300_7500.SplitData.node0442 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0443
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0441 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0442]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M7300_7500.SplitData.node0441 := by
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
  · exact treeEq0442

def B0440 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B0441, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M7300_7500.SplitData.node0440 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0441
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0439 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 655).pointIds 655), B0440, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M7300_7500.SplitData.node0439 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0440
  · rfl

def B0438 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0439, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M7300_7500.SplitData.node0438 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0439
  · rfl
  · rfl

def B0385 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B0386, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B0438]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M7300_7500.SplitData.node0385 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0386
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0438

def B0384 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0385, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M7300_7500.SplitData.node0384 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0385
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0383 : Block := .branch 113 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0384, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M7300_7500.SplitData.node0383 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0316 : Block := .branch 76 ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0316_0317, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B0383]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M7300_7500.SplitData.node0316 := by
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
  · exact treeEq0383

theorem accepted0316 : B0316.accepted = true := by decide +kernel
theorem checked0316 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0316 (maskNeeds ![385, 147934241659377681922, 11861292468192260659204, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0316]
  exact B0316.sound accepted0316
#print axioms checked0316

def B0461 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M7300_7500.SplitData.node0461 := by
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

def B0460 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0461]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M7300_7500.SplitData.node0460 := by
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
  · exact treeEq0461

def B0459 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B0460, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M7300_7500.SplitData.node0459 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0460
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0458 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0459]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M7300_7500.SplitData.node0458 := by
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
  · exact treeEq0459

def B0457 : Block := .branch 169 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B0458, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M7300_7500.SplitData.node0457 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0458
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0456 : Block := .branch 170 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 679).pointIds 679), B0457, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M7300_7500.SplitData.node0456 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl

def B0466 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M7300_7500.SplitData.node0466 := by
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

def B0465 : Block := .branch 171 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0466]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M7300_7500.SplitData.node0465 := by
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
  · exact treeEq0466

def B0464 : Block := .branch 170 ![385, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), B0465, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M7300_7500.SplitData.node0464 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0465
  · rfl
  · rfl

def B0463 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0464, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M7300_7500.SplitData.node0463 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0464
  · rfl

def B0462 : Block := .branch 168 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B0463, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M7300_7500.SplitData.node0462 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0463
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0455 : Block := .branch 108 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B0456, (.leaf 5 (Common.fact 308).pointIds 308), B0462]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M7300_7500.SplitData.node0455 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0456
  · rfl
  · exact treeEq0462

theorem accepted0455 : B0455.accepted = true := by decide +kernel
theorem checked0455 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0455 (maskNeeds ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0455]
  exact B0455.sound accepted0455
#print axioms checked0455

def Tip0453_0455 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0455 ![2535301200456458802993406411137, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0455
def B0474 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M7300_7500.SplitData.node0474 := by
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

def B0473 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0474, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M7300_7500.SplitData.node0473 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0474
  · rfl
  · rfl

def B0472 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0473]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M7300_7500.SplitData.node0472 := by
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
  · exact treeEq0473

def B0471 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B0472, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M7300_7500.SplitData.node0471 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0472
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0470 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0471]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M7300_7500.SplitData.node0470 := by
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
  · exact treeEq0471

def B0469 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B0470, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M7300_7500.SplitData.node0469 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0470
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0468 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0469, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M7300_7500.SplitData.node0468 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0469
  · rfl

def B0467 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0468, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M7300_7500.SplitData.node0467 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0468
  · rfl
  · rfl

def B0454 : Block := .branch 101 ![2475880078570760549798248833, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0453_0455, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0467]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M7300_7500.SplitData.node0454 := by
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
  · exact treeEq0467

def B0482 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M7300_7500.SplitData.node0482 := by
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

def B0481 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0482, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M7300_7500.SplitData.node0481 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0482
  · rfl
  · rfl

def B0480 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0481]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M7300_7500.SplitData.node0480 := by
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
  · exact treeEq0481

def B0479 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B0480, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0479 : B0479.tree = HexagonCover.NBand.M7300_7500.SplitData.node0479 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0480
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0478 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0479]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M7300_7500.SplitData.node0478 := by
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
  · exact treeEq0479

def B0477 : Block := .branch 169 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B0478, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 763).pointIds 763), (.leaf 3 (Common.fact 764).pointIds 764), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M7300_7500.SplitData.node0477 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0478
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0476 : Block := .branch 170 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 761).pointIds 761), (.leaf 3 (Common.fact 762).pointIds 762), (.leaf 4 (Common.fact 655).pointIds 655), B0477, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M7300_7500.SplitData.node0476 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0477
  · rfl

def B0475 : Block := .branch 171 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 765).pointIds 765), (.leaf 3 (Common.fact 766).pointIds 766), B0476, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M7300_7500.SplitData.node0475 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0476
  · rfl
  · rfl

def B0453 : Block := .branch 91 ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0454, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B0475]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M7300_7500.SplitData.node0453 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0454
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0475

theorem accepted0453 : B0453.accepted = true := by decide +kernel
theorem checked0453 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0453 (maskNeeds ![385, 147934241659377681922, 7138925985322615445508, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0453]
  exact B0453.sound accepted0453
#print axioms checked0453

end HexagonCover.NBand.M7300_7500.SplitTree.Run0005
