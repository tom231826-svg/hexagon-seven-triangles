import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0034
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0035
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2330_2332 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2332 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0034.checked2332
def B2482 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2482 : B2482.tree = HexagonCover.NBand.M7300_7500.SplitData.node2482 := by
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

def B2481 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2482]
theorem treeEq2481 : B2481.tree = HexagonCover.NBand.M7300_7500.SplitData.node2481 := by
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
  · exact treeEq2482

def B2480 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2481, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2480 : B2480.tree = HexagonCover.NBand.M7300_7500.SplitData.node2480 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2481
  · rfl
  · rfl

def B2479 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2480, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2479 : B2479.tree = HexagonCover.NBand.M7300_7500.SplitData.node2479 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2480
  · rfl

def B2478 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2479, (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2478 : B2478.tree = HexagonCover.NBand.M7300_7500.SplitData.node2478 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2479
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2477 : Block := .branch 163 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2478]
theorem treeEq2477 : B2477.tree = HexagonCover.NBand.M7300_7500.SplitData.node2477 := by
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
  · exact treeEq2478

def B2476 : Block := .branch 165 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2477, (.leaf 0 [] 0)]
theorem treeEq2476 : B2476.tree = HexagonCover.NBand.M7300_7500.SplitData.node2476 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2477
  · rfl

def B2475 : Block := .branch 167 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2476, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2475 : B2475.tree = HexagonCover.NBand.M7300_7500.SplitData.node2475 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2476
  · rfl

def B2474 : Block := .branch 142 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2475, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2474 : B2474.tree = HexagonCover.NBand.M7300_7500.SplitData.node2474 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2475
  · rfl
  · rfl

def B2473 : Block := .branch 144 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2474, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2473 : B2473.tree = HexagonCover.NBand.M7300_7500.SplitData.node2473 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2474
  · rfl

def B2472 : Block := .branch 161 ![385, 144257025075840514, 18518801667747485700, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 829).pointIds 829), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2473]
theorem treeEq2472 : B2472.tree = HexagonCover.NBand.M7300_7500.SplitData.node2472 := by
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
  · exact treeEq2473

def B2331 : Block := .branch 71 ![385, 147718209614752253442, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip2330_2332, B2472, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq2331 : B2331.tree = HexagonCover.NBand.M7300_7500.SplitData.node2331 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2472
  · rfl
  · rfl
  · rfl

def B2489 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 810).pointIds 810), (.leaf 2 (Common.fact 811).pointIds 811), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq2489 : B2489.tree = HexagonCover.NBand.M7300_7500.SplitData.node2489 := by
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
  · rfl

def B2488 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![B2489, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2488 : B2488.tree = HexagonCover.NBand.M7300_7500.SplitData.node2488 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2489
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2487 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 753).pointIds 753), B2488, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2487 : B2487.tree = HexagonCover.NBand.M7300_7500.SplitData.node2487 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2486 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2487]
theorem treeEq2486 : B2486.tree = HexagonCover.NBand.M7300_7500.SplitData.node2486 := by
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
  · exact treeEq2487

def B2485 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![B2486, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2485 : B2485.tree = HexagonCover.NBand.M7300_7500.SplitData.node2485 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2486
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2484 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2485, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2484 : B2484.tree = HexagonCover.NBand.M7300_7500.SplitData.node2484 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2485
  · rfl

def B2483 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2484, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2483 : B2483.tree = HexagonCover.NBand.M7300_7500.SplitData.node2483 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2484
  · rfl
  · rfl

def B2330 : Block := .branch 67 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 198).pointIds 198), B2331, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B2483]
theorem treeEq2330 : B2330.tree = HexagonCover.NBand.M7300_7500.SplitData.node2330 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2331
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2483

theorem accepted2330 : B2330.accepted = true := by decide +kernel
theorem checked2330 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2330 (maskNeeds ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2330]
  exact B2330.sound accepted2330
#print axioms checked2330

def Tip2318_2330 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2330 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2330
def B2323 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2323 : B2323.tree = HexagonCover.NBand.M7300_7500.SplitData.node2323 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2322 : Block := .branch 171 ![288230376151712129, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2323]
theorem treeEq2322 : B2322.tree = HexagonCover.NBand.M7300_7500.SplitData.node2322 := by
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
  · exact treeEq2323

def B2321 : Block := .branch 170 ![288230376151712129, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2322, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2321 : B2321.tree = HexagonCover.NBand.M7300_7500.SplitData.node2321 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2322
  · rfl
  · rfl

def B2320 : Block := .branch 169 ![288230376151712129, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 800).pointIds 800), (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2321, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2320 : B2320.tree = HexagonCover.NBand.M7300_7500.SplitData.node2320 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2321
  · rfl

def B2328 : Block := .branch 91 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2328 : B2328.tree = HexagonCover.NBand.M7300_7500.SplitData.node2328 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2327 : Block := .branch 171 ![576460752303423873, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2328]
theorem treeEq2327 : B2327.tree = HexagonCover.NBand.M7300_7500.SplitData.node2327 := by
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
  · exact treeEq2328

def B2326 : Block := .branch 170 ![576460752303423873, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), B2327, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2326 : B2326.tree = HexagonCover.NBand.M7300_7500.SplitData.node2326 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2327
  · rfl
  · rfl

def B2325 : Block := .branch 169 ![576460752303423873, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 808).pointIds 808), (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2326, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2325 : B2325.tree = HexagonCover.NBand.M7300_7500.SplitData.node2325 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2326
  · rfl

def B2495 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 847).pointIds 847), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2495 : B2495.tree = HexagonCover.NBand.M7300_7500.SplitData.node2495 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2494 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B2495, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq2494 : B2494.tree = HexagonCover.NBand.M7300_7500.SplitData.node2494 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2495
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2493 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2494]
theorem treeEq2493 : B2493.tree = HexagonCover.NBand.M7300_7500.SplitData.node2493 := by
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
  · exact treeEq2494

def B2492 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539264657732307602899008] ![B2493, (.leaf 1 (Common.fact 801).pointIds 801), (.leaf 2 (Common.fact 802).pointIds 802), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2492 : B2492.tree = HexagonCover.NBand.M7300_7500.SplitData.node2492 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2493
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2491 : Block := .branch 170 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 803).pointIds 803), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2492, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2491 : B2491.tree = HexagonCover.NBand.M7300_7500.SplitData.node2491 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2492
  · rfl

def B2490 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 805).pointIds 805), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 620).pointIds 620), B2491, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2490 : B2490.tree = HexagonCover.NBand.M7300_7500.SplitData.node2490 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2491
  · rfl
  · rfl

def B2329 : Block := .branch 65 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), Tip2318_2330, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B2490]
theorem treeEq2329 : B2329.tree = HexagonCover.NBand.M7300_7500.SplitData.node2329 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2490

def B2324 : Block := .branch 59 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2325, B2329, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq2324 : B2324.tree = HexagonCover.NBand.M7300_7500.SplitData.node2324 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2325
  · exact treeEq2329
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2319 : Block := .branch 58 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2320, B2324, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq2319 : B2319.tree = HexagonCover.NBand.M7300_7500.SplitData.node2319 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2320
  · exact treeEq2324
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2318 : Block := .branch 87 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B2319]
theorem treeEq2318 : B2318.tree = HexagonCover.NBand.M7300_7500.SplitData.node2318 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2319

theorem accepted2318 : B2318.accepted = true := by decide +kernel
theorem checked2318 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2318 (maskNeeds ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936]) := by
  rw [← treeEq2318]
  exact B2318.sound accepted2318
#print axioms checked2318

def B2527 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq2527 : B2527.tree = HexagonCover.NBand.M7300_7500.SplitData.node2527 := by
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

def B2526 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2527]
theorem treeEq2526 : B2526.tree = HexagonCover.NBand.M7300_7500.SplitData.node2526 := by
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
  · exact treeEq2527

def B2525 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2526, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2525 : B2525.tree = HexagonCover.NBand.M7300_7500.SplitData.node2525 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2524 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2525]
theorem treeEq2524 : B2524.tree = HexagonCover.NBand.M7300_7500.SplitData.node2524 := by
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
  · exact treeEq2525

def B2523 : Block := .branch 169 ![2535301200456458802993406411137, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2524, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2523 : B2523.tree = HexagonCover.NBand.M7300_7500.SplitData.node2523 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2524
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2522 : Block := .branch 170 ![2535301200456458802993406411137, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B2523, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2522 : B2522.tree = HexagonCover.NBand.M7300_7500.SplitData.node2522 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2523
  · rfl

def B2535 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq2535 : B2535.tree = HexagonCover.NBand.M7300_7500.SplitData.node2535 := by
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
  · rfl

def B2534 : Block := .branch 100 ![385, 1461501637330902918204303802735925710892893734402, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B2535, (.leaf 1 (Common.fact 432).pointIds 432), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq2534 : B2534.tree = HexagonCover.NBand.M7300_7500.SplitData.node2534 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2535
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2533 : Block := .branch 160 ![385, 618970019642691236961191426, 18446884811197913092, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B2534, (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq2533 : B2533.tree = HexagonCover.NBand.M7300_7500.SplitData.node2533 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2534
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2532 : Block := .branch 162 ![385, 618970019642691236961191426, 18446884811197913092, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2533, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq2532 : B2532.tree = HexagonCover.NBand.M7300_7500.SplitData.node2532 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2533
  · rfl
  · rfl
  · rfl

def B2531 : Block := .branch 171 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2532]
theorem treeEq2531 : B2531.tree = HexagonCover.NBand.M7300_7500.SplitData.node2531 := by
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
  · exact treeEq2532

def B2530 : Block := .branch 170 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2531, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2530 : B2530.tree = HexagonCover.NBand.M7300_7500.SplitData.node2530 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2531
  · rfl
  · rfl

def B2529 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2530, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2529 : B2529.tree = HexagonCover.NBand.M7300_7500.SplitData.node2529 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2530
  · rfl

def B2528 : Block := .branch 168 ![2535301200456458802993406411137, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B2529, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq2528 : B2528.tree = HexagonCover.NBand.M7300_7500.SplitData.node2528 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2529
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2521 : Block := .branch 108 ![2535301200456458802993406411137, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B2522, (.leaf 5 (Common.fact 308).pointIds 308), B2528]
theorem treeEq2521 : B2521.tree = HexagonCover.NBand.M7300_7500.SplitData.node2521 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2522
  · rfl
  · exact treeEq2528

theorem accepted2521 : B2521.accepted = true := by decide +kernel
theorem checked2521 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2521 (maskNeeds ![2535301200456458802993406411137, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2521]
  exact B2521.sound accepted2521
#print axioms checked2521

def Tip2519_2521 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2521 ![2535301200456458802993406411137, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked2521
def B2543 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq2543 : B2543.tree = HexagonCover.NBand.M7300_7500.SplitData.node2543 := by
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

def B2542 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2543, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq2542 : B2542.tree = HexagonCover.NBand.M7300_7500.SplitData.node2542 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2543
  · rfl
  · rfl

def B2541 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2542]
theorem treeEq2541 : B2541.tree = HexagonCover.NBand.M7300_7500.SplitData.node2541 := by
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
  · exact treeEq2542

def B2540 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B2541, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2540 : B2540.tree = HexagonCover.NBand.M7300_7500.SplitData.node2540 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2541
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2539 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2540]
theorem treeEq2539 : B2539.tree = HexagonCover.NBand.M7300_7500.SplitData.node2539 := by
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
  · exact treeEq2540

def B2538 : Block := .branch 169 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B2539, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2538 : B2538.tree = HexagonCover.NBand.M7300_7500.SplitData.node2538 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2539
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2537 : Block := .branch 170 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2538, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2537 : B2537.tree = HexagonCover.NBand.M7300_7500.SplitData.node2537 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2538
  · rfl

def B2536 : Block := .branch 171 ![2475880078570760549798248833, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2537, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq2536 : B2536.tree = HexagonCover.NBand.M7300_7500.SplitData.node2536 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2537
  · rfl
  · rfl

def B2520 : Block := .branch 101 ![2475880078570760549798248833, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2519_2521, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B2536]
theorem treeEq2520 : B2520.tree = HexagonCover.NBand.M7300_7500.SplitData.node2520 := by
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
  · exact treeEq2536

def B2551 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2551 : B2551.tree = HexagonCover.NBand.M7300_7500.SplitData.node2551 := by
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

def B2550 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2551, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2550 : B2550.tree = HexagonCover.NBand.M7300_7500.SplitData.node2550 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2551
  · rfl
  · rfl

def B2549 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2550]
theorem treeEq2549 : B2549.tree = HexagonCover.NBand.M7300_7500.SplitData.node2549 := by
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
  · exact treeEq2550

def B2548 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B2549, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2548 : B2548.tree = HexagonCover.NBand.M7300_7500.SplitData.node2548 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2549
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2547 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2548]
theorem treeEq2547 : B2547.tree = HexagonCover.NBand.M7300_7500.SplitData.node2547 := by
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
  · exact treeEq2548

def B2546 : Block := .branch 169 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B2547, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2546 : B2546.tree = HexagonCover.NBand.M7300_7500.SplitData.node2546 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2547
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2545 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2546, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2545 : B2545.tree = HexagonCover.NBand.M7300_7500.SplitData.node2545 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2546
  · rfl

def B2544 : Block := .branch 171 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2545, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2544 : B2544.tree = HexagonCover.NBand.M7300_7500.SplitData.node2544 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2545
  · rfl
  · rfl

def B2519 : Block := .branch 91 ![385, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B2520, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B2544]
theorem treeEq2519 : B2519.tree = HexagonCover.NBand.M7300_7500.SplitData.node2519 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2520
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2544

theorem accepted2519 : B2519.accepted = true := by decide +kernel
theorem checked2519 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2519 (maskNeeds ![385, 618970019858864019074975234, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2519]
  exact B2519.sound accepted2519
#print axioms checked2519

end HexagonCover.NBand.M7300_7500.SplitTree.Run0035
