import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0036
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0037
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2513_2514 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2514 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0036.checked2514
def B2628 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2628 : B2628.tree = HexagonCover.NBand.M7300_7500.SplitData.node2628 := by
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

def B2627 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2628]
theorem treeEq2627 : B2627.tree = HexagonCover.NBand.M7300_7500.SplitData.node2627 := by
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
  · exact treeEq2628

def B2626 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2627, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2626 : B2626.tree = HexagonCover.NBand.M7300_7500.SplitData.node2626 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2627
  · rfl
  · rfl

def B2625 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2626, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2625 : B2625.tree = HexagonCover.NBand.M7300_7500.SplitData.node2625 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2626
  · rfl

def B2624 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2625, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2624 : B2624.tree = HexagonCover.NBand.M7300_7500.SplitData.node2624 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2623 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2624]
theorem treeEq2623 : B2623.tree = HexagonCover.NBand.M7300_7500.SplitData.node2623 := by
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
  · exact treeEq2624

def B2622 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2623, (.leaf 0 [] 0)]
theorem treeEq2622 : B2622.tree = HexagonCover.NBand.M7300_7500.SplitData.node2622 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2623
  · rfl

def B2621 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2622, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2621 : B2621.tree = HexagonCover.NBand.M7300_7500.SplitData.node2621 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2622
  · rfl

def B2620 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2621, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2620 : B2620.tree = HexagonCover.NBand.M7300_7500.SplitData.node2620 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2621
  · rfl
  · rfl

def B2619 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2620, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2619 : B2619.tree = HexagonCover.NBand.M7300_7500.SplitData.node2619 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2620
  · rfl

def B2618 : Block := .branch 161 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 830).pointIds 830), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2619]
theorem treeEq2618 : B2618.tree = HexagonCover.NBand.M7300_7500.SplitData.node2618 := by
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
  · exact treeEq2619

def B2513 : Block := .branch 74 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip2513_2514, B2618, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq2513 : B2513.tree = HexagonCover.NBand.M7300_7500.SplitData.node2513 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2618
  · rfl
  · rfl
  · rfl

theorem accepted2513 : B2513.accepted = true := by decide +kernel
theorem checked2513 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2513 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2513]
  exact B2513.sound accepted2513
#print axioms checked2513

def Tip2512_2513 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2513 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2513
def B2639 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2639 : B2639.tree = HexagonCover.NBand.M7300_7500.SplitData.node2639 := by
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

def B2638 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2639]
theorem treeEq2638 : B2638.tree = HexagonCover.NBand.M7300_7500.SplitData.node2638 := by
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
  · exact treeEq2639

def B2637 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2638, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2637 : B2637.tree = HexagonCover.NBand.M7300_7500.SplitData.node2637 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2638
  · rfl
  · rfl

def B2636 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2637, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2636 : B2636.tree = HexagonCover.NBand.M7300_7500.SplitData.node2636 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2637
  · rfl

def B2635 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2636, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2635 : B2635.tree = HexagonCover.NBand.M7300_7500.SplitData.node2635 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2636
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2634 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2635]
theorem treeEq2634 : B2634.tree = HexagonCover.NBand.M7300_7500.SplitData.node2634 := by
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
  · exact treeEq2635

def B2633 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2634, (.leaf 0 [] 0)]
theorem treeEq2633 : B2633.tree = HexagonCover.NBand.M7300_7500.SplitData.node2633 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2634
  · rfl

def B2632 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2633, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2632 : B2632.tree = HexagonCover.NBand.M7300_7500.SplitData.node2632 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2633
  · rfl

def B2631 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2632, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2631 : B2631.tree = HexagonCover.NBand.M7300_7500.SplitData.node2631 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2632
  · rfl
  · rfl

def B2630 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2631, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2630 : B2630.tree = HexagonCover.NBand.M7300_7500.SplitData.node2630 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2631
  · rfl

def B2629 : Block := .branch 161 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2630]
theorem treeEq2629 : B2629.tree = HexagonCover.NBand.M7300_7500.SplitData.node2629 := by
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
  · exact treeEq2630

def B2512 : Block := .branch 73 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip2512_2513, B2629, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq2512 : B2512.tree = HexagonCover.NBand.M7300_7500.SplitData.node2512 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2629
  · rfl
  · rfl
  · rfl

theorem accepted2512 : B2512.accepted = true := by decide +kernel
theorem checked2512 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2512 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2512]
  exact B2512.sound accepted2512
#print axioms checked2512

def Tip2511_2512 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2512 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2512
def B2650 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2650 : B2650.tree = HexagonCover.NBand.M7300_7500.SplitData.node2650 := by
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

def B2649 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2650]
theorem treeEq2649 : B2649.tree = HexagonCover.NBand.M7300_7500.SplitData.node2649 := by
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
  · exact treeEq2650

def B2648 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2649, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2648 : B2648.tree = HexagonCover.NBand.M7300_7500.SplitData.node2648 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2649
  · rfl
  · rfl

def B2647 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2648, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2647 : B2647.tree = HexagonCover.NBand.M7300_7500.SplitData.node2647 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2648
  · rfl

def B2646 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2647, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2646 : B2646.tree = HexagonCover.NBand.M7300_7500.SplitData.node2646 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2647
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2645 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2646]
theorem treeEq2645 : B2645.tree = HexagonCover.NBand.M7300_7500.SplitData.node2645 := by
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
  · exact treeEq2646

def B2644 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2645, (.leaf 0 [] 0)]
theorem treeEq2644 : B2644.tree = HexagonCover.NBand.M7300_7500.SplitData.node2644 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2645
  · rfl

def B2643 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2644, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2643 : B2643.tree = HexagonCover.NBand.M7300_7500.SplitData.node2643 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2644
  · rfl

def B2642 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2643, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2642 : B2642.tree = HexagonCover.NBand.M7300_7500.SplitData.node2642 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2643
  · rfl
  · rfl

def B2641 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2642, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2641 : B2641.tree = HexagonCover.NBand.M7300_7500.SplitData.node2641 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2642
  · rfl

def B2640 : Block := .branch 161 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 841).pointIds 841), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2641]
theorem treeEq2640 : B2640.tree = HexagonCover.NBand.M7300_7500.SplitData.node2640 := by
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
  · exact treeEq2641

def B2511 : Block := .branch 72 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip2511_2512, B2640, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2511 : B2511.tree = HexagonCover.NBand.M7300_7500.SplitData.node2511 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2640
  · rfl
  · rfl
  · rfl

theorem accepted2511 : B2511.accepted = true := by decide +kernel
theorem checked2511 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2511 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2511]
  exact B2511.sound accepted2511
#print axioms checked2511

def Tip2509_2511 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2511 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2511
def B2661 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq2661 : B2661.tree = HexagonCover.NBand.M7300_7500.SplitData.node2661 := by
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

def B2660 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 1496577682202030887873229054085403380289765300600848, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 837).pointIds 837), (.leaf 5 (Common.fact 656).pointIds 656), B2661]
theorem treeEq2660 : B2660.tree = HexagonCover.NBand.M7300_7500.SplitData.node2660 := by
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
  · exact treeEq2661

def B2659 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 233840261972987002208454690542538204970878178295840, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2660, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2659 : B2659.tree = HexagonCover.NBand.M7300_7500.SplitData.node2659 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2660
  · rfl
  · rfl

def B2658 : Block := .branch 125 ![374144419156711147060143317175368453031918731002241, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 5575186299632655785383929568162090376593424, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 572).pointIds 572), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2659, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2658 : B2658.tree = HexagonCover.NBand.M7300_7500.SplitData.node2658 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2659
  · rfl

def B2657 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2658, (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2657 : B2657.tree = HexagonCover.NBand.M7300_7500.SplitData.node2657 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2658
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2656 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2657]
theorem treeEq2656 : B2656.tree = HexagonCover.NBand.M7300_7500.SplitData.node2656 := by
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
  · exact treeEq2657

def B2655 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2656, (.leaf 0 [] 0)]
theorem treeEq2655 : B2655.tree = HexagonCover.NBand.M7300_7500.SplitData.node2655 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2656
  · rfl

def B2654 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2655, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2654 : B2654.tree = HexagonCover.NBand.M7300_7500.SplitData.node2654 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2655
  · rfl

def B2653 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2654, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2653 : B2653.tree = HexagonCover.NBand.M7300_7500.SplitData.node2653 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2654
  · rfl
  · rfl

def B2652 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2653, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2652 : B2652.tree = HexagonCover.NBand.M7300_7500.SplitData.node2652 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2653
  · rfl

def B2651 : Block := .branch 161 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2652]
theorem treeEq2651 : B2651.tree = HexagonCover.NBand.M7300_7500.SplitData.node2651 := by
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
  · exact treeEq2652

def B2510 : Block := .branch 71 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip2509_2511, B2651, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq2510 : B2510.tree = HexagonCover.NBand.M7300_7500.SplitData.node2510 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2651
  · rfl
  · rfl
  · rfl

def B2668 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq2668 : B2668.tree = HexagonCover.NBand.M7300_7500.SplitData.node2668 := by
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

def B2667 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![B2668, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2667 : B2667.tree = HexagonCover.NBand.M7300_7500.SplitData.node2667 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2668
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2666 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 753).pointIds 753), B2667, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2666 : B2666.tree = HexagonCover.NBand.M7300_7500.SplitData.node2666 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2667
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2665 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2666]
theorem treeEq2665 : B2665.tree = HexagonCover.NBand.M7300_7500.SplitData.node2665 := by
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
  · exact treeEq2666

def B2664 : Block := .branch 169 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![B2665, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2664 : B2664.tree = HexagonCover.NBand.M7300_7500.SplitData.node2664 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2663 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2664, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2663 : B2663.tree = HexagonCover.NBand.M7300_7500.SplitData.node2663 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2664
  · rfl

def B2662 : Block := .branch 171 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2663, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2662 : B2662.tree = HexagonCover.NBand.M7300_7500.SplitData.node2662 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2663
  · rfl
  · rfl

def B2509 : Block := .branch 67 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 198).pointIds 198), B2510, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B2662]
theorem treeEq2509 : B2509.tree = HexagonCover.NBand.M7300_7500.SplitData.node2509 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2510
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2662

theorem accepted2509 : B2509.accepted = true := by decide +kernel
theorem checked2509 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2509 (maskNeeds ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2509]
  exact B2509.sound accepted2509
#print axioms checked2509

def B2704 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq2704 : B2704.tree = HexagonCover.NBand.M7300_7500.SplitData.node2704 := by
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

def B2703 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B2704]
theorem treeEq2703 : B2703.tree = HexagonCover.NBand.M7300_7500.SplitData.node2703 := by
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
  · exact treeEq2704

def B2702 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2703, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2702 : B2702.tree = HexagonCover.NBand.M7300_7500.SplitData.node2702 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2703
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2701 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2702]
theorem treeEq2701 : B2701.tree = HexagonCover.NBand.M7300_7500.SplitData.node2701 := by
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
  · exact treeEq2702

def B2700 : Block := .branch 169 ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2701, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2700 : B2700.tree = HexagonCover.NBand.M7300_7500.SplitData.node2700 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2701
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2699 : Block := .branch 170 ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846353304459082801411451530724212047888, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B2700, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2699 : B2699.tree = HexagonCover.NBand.M7300_7500.SplitData.node2699 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2700
  · rfl

def B2712 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq2712 : B2712.tree = HexagonCover.NBand.M7300_7500.SplitData.node2712 := by
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

def B2711 : Block := .branch 100 ![385, 1461501637330902918204303802735925710892893734402, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B2712, (.leaf 1 (Common.fact 432).pointIds 432), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq2711 : B2711.tree = HexagonCover.NBand.M7300_7500.SplitData.node2711 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2710 : Block := .branch 160 ![385, 618970019642691236961191426, 18446884811197913092, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B2711, (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq2710 : B2710.tree = HexagonCover.NBand.M7300_7500.SplitData.node2710 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2711
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2709 : Block := .branch 162 ![385, 618970019642691236961191426, 18446884811197913092, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2710, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq2709 : B2709.tree = HexagonCover.NBand.M7300_7500.SplitData.node2709 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2710
  · rfl
  · rfl
  · rfl

def B2708 : Block := .branch 171 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2709]
theorem treeEq2708 : B2708.tree = HexagonCover.NBand.M7300_7500.SplitData.node2708 := by
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
  · exact treeEq2709

def B2707 : Block := .branch 170 ![385, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2708, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2707 : B2707.tree = HexagonCover.NBand.M7300_7500.SplitData.node2707 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2708
  · rfl
  · rfl

def B2706 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071807775992197654491027316204372032] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2707, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2706 : B2706.tree = HexagonCover.NBand.M7300_7500.SplitData.node2706 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2707
  · rfl

def B2705 : Block := .branch 168 ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071807775992197654491027316204372032] ![B2706, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq2705 : B2705.tree = HexagonCover.NBand.M7300_7500.SplitData.node2705 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2706
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2698 : Block := .branch 108 ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B2699, (.leaf 5 (Common.fact 308).pointIds 308), B2705]
theorem treeEq2698 : B2698.tree = HexagonCover.NBand.M7300_7500.SplitData.node2698 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2699
  · rfl
  · exact treeEq2705

theorem accepted2698 : B2698.accepted = true := by decide +kernel
theorem checked2698 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2698 (maskNeeds ![2535301200456458802993406411137, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2698]
  exact B2698.sound accepted2698
#print axioms checked2698

end HexagonCover.NBand.M7300_7500.SplitTree.Run0037
