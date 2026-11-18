import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0033
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0034
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2336_2338 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2338 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0033.checked2338
def B2397 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq2397 : B2397.tree = HexagonCover.NBand.M7300_7500.SplitData.node2397 := by
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

def B2396 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B2397, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq2396 : B2396.tree = HexagonCover.NBand.M7300_7500.SplitData.node2396 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2397
  · rfl
  · rfl

def B2395 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B2396, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq2395 : B2395.tree = HexagonCover.NBand.M7300_7500.SplitData.node2395 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2396
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2394 : Block := .branch 160 ![385, 302821750855852999312898, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 817).pointIds 817), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2395]
theorem treeEq2394 : B2394.tree = HexagonCover.NBand.M7300_7500.SplitData.node2394 := by
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
  · exact treeEq2395

def B2393 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B2394, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq2393 : B2393.tree = HexagonCover.NBand.M7300_7500.SplitData.node2393 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2394
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2392 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231455045494293661186, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2393]
theorem treeEq2392 : B2392.tree = HexagonCover.NBand.M7300_7500.SplitData.node2392 := by
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
  · exact treeEq2393

def B2391 : Block := .branch 169 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B2392, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2391 : B2391.tree = HexagonCover.NBand.M7300_7500.SplitData.node2391 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2392
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2390 : Block := .branch 170 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2391, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2390 : B2390.tree = HexagonCover.NBand.M7300_7500.SplitData.node2390 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2391
  · rfl

def B2389 : Block := .branch 171 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2390, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq2389 : B2389.tree = HexagonCover.NBand.M7300_7500.SplitData.node2389 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2390
  · rfl
  · rfl

def B2337 : Block := .branch 80 ![385, 302231599160682369517058, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2336_2338, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B2389]
theorem treeEq2337 : B2337.tree = HexagonCover.NBand.M7300_7500.SplitData.node2337 := by
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
  · exact treeEq2389

def B2405 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2405 : B2405.tree = HexagonCover.NBand.M7300_7500.SplitData.node2405 := by
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

def B2404 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2405, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2404 : B2404.tree = HexagonCover.NBand.M7300_7500.SplitData.node2404 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2405
  · rfl
  · rfl

def B2403 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2404]
theorem treeEq2403 : B2403.tree = HexagonCover.NBand.M7300_7500.SplitData.node2403 := by
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
  · exact treeEq2404

def B2402 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B2403, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2402 : B2402.tree = HexagonCover.NBand.M7300_7500.SplitData.node2402 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2403
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2401 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2402]
theorem treeEq2401 : B2401.tree = HexagonCover.NBand.M7300_7500.SplitData.node2401 := by
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
  · exact treeEq2402

def B2400 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B2401, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2400 : B2400.tree = HexagonCover.NBand.M7300_7500.SplitData.node2400 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2401
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2399 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2400, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2399 : B2399.tree = HexagonCover.NBand.M7300_7500.SplitData.node2399 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2400
  · rfl

def B2398 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2399, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq2398 : B2398.tree = HexagonCover.NBand.M7300_7500.SplitData.node2398 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2399
  · rfl
  · rfl

def B2336 : Block := .branch 78 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B2337, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B2398]
theorem treeEq2336 : B2336.tree = HexagonCover.NBand.M7300_7500.SplitData.node2336 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2337
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2398

theorem accepted2336 : B2336.accepted = true := by decide +kernel
theorem checked2336 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2336 (maskNeeds ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2336]
  exact B2336.sound accepted2336
#print axioms checked2336

def Tip2335_2409 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2409 ![10384596192949733827821542456689025, 442866114794105079298, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0033.checked2409
def Tip2335_2336 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2336 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2336
def B2438 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5316911983139663491615228241121476624, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 725).pointIds 725), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq2438 : B2438.tree = HexagonCover.NBand.M7300_7500.SplitData.node2438 := by
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

def B2437 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), B2438, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq2437 : B2437.tree = HexagonCover.NBand.M7300_7500.SplitData.node2437 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2438
  · rfl
  · rfl

def B2436 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2437]
theorem treeEq2436 : B2436.tree = HexagonCover.NBand.M7300_7500.SplitData.node2436 := by
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
  · exact treeEq2437

def B2435 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B2436, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2435 : B2435.tree = HexagonCover.NBand.M7300_7500.SplitData.node2435 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2436
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2434 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B2435, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2434 : B2434.tree = HexagonCover.NBand.M7300_7500.SplitData.node2434 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2435
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2433 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2434]
theorem treeEq2433 : B2433.tree = HexagonCover.NBand.M7300_7500.SplitData.node2433 := by
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
  · exact treeEq2434

def B2432 : Block := .branch 169 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B2433, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2432 : B2432.tree = HexagonCover.NBand.M7300_7500.SplitData.node2432 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2433
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2431 : Block := .branch 170 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2432, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2431 : B2431.tree = HexagonCover.NBand.M7300_7500.SplitData.node2431 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2432
  · rfl

def B2430 : Block := .branch 171 ![2475880078570760549798248833, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2431, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq2430 : B2430.tree = HexagonCover.NBand.M7300_7500.SplitData.node2430 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2431
  · rfl
  · rfl

def B2408 : Block := .branch 68 ![10384596192949733827821542456689025, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2335_2409, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B2430]
theorem treeEq2408 : B2408.tree = HexagonCover.NBand.M7300_7500.SplitData.node2408 := by
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
  · exact treeEq2430

def B2407 : Block := .branch 91 ![10384593717069655257060992658440577, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2408, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2407 : B2407.tree = HexagonCover.NBand.M7300_7500.SplitData.node2407 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2408
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2406 : Block := .branch 113 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2407, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2406 : B2406.tree = HexagonCover.NBand.M7300_7500.SplitData.node2406 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2407
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2335 : Block := .branch 76 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip2335_2336, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B2406]
theorem treeEq2335 : B2335.tree = HexagonCover.NBand.M7300_7500.SplitData.node2335 := by
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
  · exact treeEq2406

theorem accepted2335 : B2335.accepted = true := by decide +kernel
theorem checked2335 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2335 (maskNeeds ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2335]
  exact B2335.sound accepted2335
#print axioms checked2335

def Tip2334_2335 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2335 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2335
def B2449 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2449 : B2449.tree = HexagonCover.NBand.M7300_7500.SplitData.node2449 := by
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

def B2448 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2449]
theorem treeEq2448 : B2448.tree = HexagonCover.NBand.M7300_7500.SplitData.node2448 := by
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
  · exact treeEq2449

def B2447 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2448, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2447 : B2447.tree = HexagonCover.NBand.M7300_7500.SplitData.node2447 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2448
  · rfl
  · rfl

def B2446 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2447, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2446 : B2446.tree = HexagonCover.NBand.M7300_7500.SplitData.node2446 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2447
  · rfl

def B2445 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2446, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2445 : B2445.tree = HexagonCover.NBand.M7300_7500.SplitData.node2445 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2446
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2444 : Block := .branch 163 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2445]
theorem treeEq2444 : B2444.tree = HexagonCover.NBand.M7300_7500.SplitData.node2444 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2445

def B2443 : Block := .branch 165 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2444, (.leaf 0 [] 0)]
theorem treeEq2443 : B2443.tree = HexagonCover.NBand.M7300_7500.SplitData.node2443 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2444
  · rfl

def B2442 : Block := .branch 167 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2443, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2442 : B2442.tree = HexagonCover.NBand.M7300_7500.SplitData.node2442 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2443
  · rfl

def B2441 : Block := .branch 142 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2442, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2441 : B2441.tree = HexagonCover.NBand.M7300_7500.SplitData.node2441 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2442
  · rfl
  · rfl

def B2440 : Block := .branch 144 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2441, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2440 : B2440.tree = HexagonCover.NBand.M7300_7500.SplitData.node2440 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2441
  · rfl

def B2439 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 829).pointIds 829), (.leaf 3 (Common.fact 830).pointIds 830), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2440]
theorem treeEq2439 : B2439.tree = HexagonCover.NBand.M7300_7500.SplitData.node2439 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2440

def B2334 : Block := .branch 74 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip2334_2335, B2439, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq2334 : B2334.tree = HexagonCover.NBand.M7300_7500.SplitData.node2334 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2439
  · rfl
  · rfl
  · rfl

theorem accepted2334 : B2334.accepted = true := by decide +kernel
theorem checked2334 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2334 (maskNeeds ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2334]
  exact B2334.sound accepted2334
#print axioms checked2334

def Tip2333_2334 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2334 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2334
def B2460 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2460 : B2460.tree = HexagonCover.NBand.M7300_7500.SplitData.node2460 := by
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

def B2459 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2460]
theorem treeEq2459 : B2459.tree = HexagonCover.NBand.M7300_7500.SplitData.node2459 := by
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
  · exact treeEq2460

def B2458 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2459, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2458 : B2458.tree = HexagonCover.NBand.M7300_7500.SplitData.node2458 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2459
  · rfl
  · rfl

def B2457 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2458, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2457 : B2457.tree = HexagonCover.NBand.M7300_7500.SplitData.node2457 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2458
  · rfl

def B2456 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2457, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2456 : B2456.tree = HexagonCover.NBand.M7300_7500.SplitData.node2456 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2457
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2455 : Block := .branch 163 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2456]
theorem treeEq2455 : B2455.tree = HexagonCover.NBand.M7300_7500.SplitData.node2455 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2456

def B2454 : Block := .branch 165 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2455, (.leaf 0 [] 0)]
theorem treeEq2454 : B2454.tree = HexagonCover.NBand.M7300_7500.SplitData.node2454 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2455
  · rfl

def B2453 : Block := .branch 167 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2454, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2453 : B2453.tree = HexagonCover.NBand.M7300_7500.SplitData.node2453 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2454
  · rfl

def B2452 : Block := .branch 142 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2453, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2452 : B2452.tree = HexagonCover.NBand.M7300_7500.SplitData.node2452 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2453
  · rfl
  · rfl

def B2451 : Block := .branch 144 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2452, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2451 : B2451.tree = HexagonCover.NBand.M7300_7500.SplitData.node2451 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2452
  · rfl

def B2450 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 829).pointIds 829), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2451]
theorem treeEq2450 : B2450.tree = HexagonCover.NBand.M7300_7500.SplitData.node2450 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2451

def B2333 : Block := .branch 73 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip2333_2334, B2450, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq2333 : B2333.tree = HexagonCover.NBand.M7300_7500.SplitData.node2333 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2450
  · rfl
  · rfl
  · rfl

theorem accepted2333 : B2333.accepted = true := by decide +kernel
theorem checked2333 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2333 (maskNeeds ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2333]
  exact B2333.sound accepted2333
#print axioms checked2333

def Tip2332_2333 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2333 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2333
def B2471 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2471 : B2471.tree = HexagonCover.NBand.M7300_7500.SplitData.node2471 := by
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

def B2470 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2471]
theorem treeEq2470 : B2470.tree = HexagonCover.NBand.M7300_7500.SplitData.node2470 := by
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
  · exact treeEq2471

def B2469 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2470, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2469 : B2469.tree = HexagonCover.NBand.M7300_7500.SplitData.node2469 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2470
  · rfl
  · rfl

def B2468 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2469, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2468 : B2468.tree = HexagonCover.NBand.M7300_7500.SplitData.node2468 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2469
  · rfl

def B2467 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2468, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2467 : B2467.tree = HexagonCover.NBand.M7300_7500.SplitData.node2467 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2468
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2466 : Block := .branch 163 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2467]
theorem treeEq2466 : B2466.tree = HexagonCover.NBand.M7300_7500.SplitData.node2466 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2467

def B2465 : Block := .branch 165 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2466, (.leaf 0 [] 0)]
theorem treeEq2465 : B2465.tree = HexagonCover.NBand.M7300_7500.SplitData.node2465 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2466
  · rfl

def B2464 : Block := .branch 167 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2465, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2464 : B2464.tree = HexagonCover.NBand.M7300_7500.SplitData.node2464 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2465
  · rfl

def B2463 : Block := .branch 142 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2464, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2463 : B2463.tree = HexagonCover.NBand.M7300_7500.SplitData.node2463 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2464
  · rfl
  · rfl

def B2462 : Block := .branch 144 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2463, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2462 : B2462.tree = HexagonCover.NBand.M7300_7500.SplitData.node2462 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2463
  · rfl

def B2461 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 829).pointIds 829), (.leaf 3 (Common.fact 841).pointIds 841), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2462]
theorem treeEq2461 : B2461.tree = HexagonCover.NBand.M7300_7500.SplitData.node2461 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2462

def B2332 : Block := .branch 72 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip2332_2333, B2461, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2332 : B2332.tree = HexagonCover.NBand.M7300_7500.SplitData.node2332 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2461
  · rfl
  · rfl
  · rfl

theorem accepted2332 : B2332.accepted = true := by decide +kernel
theorem checked2332 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2332 (maskNeeds ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2332]
  exact B2332.sound accepted2332
#print axioms checked2332

end HexagonCover.NBand.M7300_7500.SplitTree.Run0034
