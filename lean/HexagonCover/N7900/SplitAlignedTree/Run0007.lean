import HexagonCover.N7900.SplitAlignedTree.Run0006
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0007
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0629_0630 : Block := .tip HexagonCover.N7900.SplitData.node0630 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0006.checked0630
def B0651 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0651 : B0651.tree = HexagonCover.N7900.SplitData.node0651 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0650 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0651]
theorem treeEq0650 : B0650.tree = HexagonCover.N7900.SplitData.node0650 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0651

def B0649 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0650, (.leaf 0 [] 0)]
theorem treeEq0649 : B0649.tree = HexagonCover.N7900.SplitData.node0649 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0650
  · rfl

def B0648 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0649, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0648 : B0648.tree = HexagonCover.N7900.SplitData.node0648 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0649
  · rfl

def B0647 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0648, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0647 : B0647.tree = HexagonCover.N7900.SplitData.node0647 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0648
  · rfl
  · rfl

def B0646 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0647, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0646 : B0646.tree = HexagonCover.N7900.SplitData.node0646 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0647
  · rfl

def B0655 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0655 : B0655.tree = HexagonCover.N7900.SplitData.node0655 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0654 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0655, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0654 : B0654.tree = HexagonCover.N7900.SplitData.node0654 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0655
  · rfl

def B0653 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0654, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0653 : B0653.tree = HexagonCover.N7900.SplitData.node0653 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0654
  · rfl
  · rfl

def B0652 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0653]
theorem treeEq0652 : B0652.tree = HexagonCover.N7900.SplitData.node0652 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0653

def B0645 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0646, B0652, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0645 : B0645.tree = HexagonCover.N7900.SplitData.node0645 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0646
  · exact treeEq0652
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0657 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0657 : B0657.tree = HexagonCover.N7900.SplitData.node0657 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0656 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0657, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0656 : B0656.tree = HexagonCover.N7900.SplitData.node0656 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0657
  · rfl
  · rfl

def B0644 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0645, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0656]
theorem treeEq0644 : B0644.tree = HexagonCover.N7900.SplitData.node0644 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0645
  · rfl
  · rfl
  · rfl
  · exact treeEq0656

def B0629 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0629_0630, B0644, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0629 : B0629.tree = HexagonCover.N7900.SplitData.node0629 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0644
  · rfl
  · rfl
  · rfl

theorem accepted0629 : B0629.accepted = true := by decide +kernel
theorem checked0629 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0629 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0629]
  exact B0629.sound accepted0629
#print axioms checked0629

def Tip0571_0584 : Block := .tip HexagonCover.N7900.SplitData.node0584 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0006.checked0584
def B0583 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0583 : B0583.tree = HexagonCover.N7900.SplitData.node0583 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0582 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0583, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0582 : B0582.tree = HexagonCover.N7900.SplitData.node0582 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0583
  · rfl
  · rfl

def B0581 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0582, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0581 : B0581.tree = HexagonCover.N7900.SplitData.node0581 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0582
  · rfl

def B0580 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0581]
theorem treeEq0580 : B0580.tree = HexagonCover.N7900.SplitData.node0580 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0581

def B0579 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0580]
theorem treeEq0579 : B0579.tree = HexagonCover.N7900.SplitData.node0579 := by
  change Tree.branch (159 : Fin 170) _ = Tree.branch (159 : Fin 170) _
  apply congrArg (Tree.branch (159 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0580

def B0578 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0579, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0578 : B0578.tree = HexagonCover.N7900.SplitData.node0578 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0579
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0577 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0578, Tip0571_0584, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0577 : B0577.tree = HexagonCover.N7900.SplitData.node0577 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0578
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0576 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0577]
theorem treeEq0576 : B0576.tree = HexagonCover.N7900.SplitData.node0576 := by
  change Tree.branch (132 : Fin 170) _ = Tree.branch (132 : Fin 170) _
  apply congrArg (Tree.branch (132 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0577

def B0575 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0576]
theorem treeEq0575 : B0575.tree = HexagonCover.N7900.SplitData.node0575 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0576

def B0574 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0575, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0574 : B0574.tree = HexagonCover.N7900.SplitData.node0574 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0575
  · rfl
  · rfl

def B0573 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0574, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0573 : B0573.tree = HexagonCover.N7900.SplitData.node0573 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0574
  · rfl

def B0572 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0573]
theorem treeEq0572 : B0572.tree = HexagonCover.N7900.SplitData.node0572 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0573

def B0615 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0615 : B0615.tree = HexagonCover.N7900.SplitData.node0615 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0614 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0615, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0614 : B0614.tree = HexagonCover.N7900.SplitData.node0614 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0615
  · rfl
  · rfl

def B0613 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0614, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0613 : B0613.tree = HexagonCover.N7900.SplitData.node0613 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0614
  · rfl

def B0571 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0572, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0613]
theorem treeEq0571 : B0571.tree = HexagonCover.N7900.SplitData.node0571 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0572
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0613

theorem accepted0571 : B0571.accepted = true := by decide +kernel
theorem checked0571 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0571 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0571]
  exact B0571.sound accepted0571
#print axioms checked0571

def Tip0479_0538 : Block := .tip HexagonCover.N7900.SplitData.node0538 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0006.checked0538
def Tip0479_0480 : Block := .tip HexagonCover.N7900.SplitData.node0480 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0006.checked0480
def B0537 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0537 : B0537.tree = HexagonCover.N7900.SplitData.node0537 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0536 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0537, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0536 : B0536.tree = HexagonCover.N7900.SplitData.node0536 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0537
  · rfl
  · rfl

def B0535 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0536, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0535 : B0535.tree = HexagonCover.N7900.SplitData.node0535 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0536
  · rfl

def B0534 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0535]
theorem treeEq0534 : B0534.tree = HexagonCover.N7900.SplitData.node0534 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0535

def B0533 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0534]
theorem treeEq0533 : B0533.tree = HexagonCover.N7900.SplitData.node0533 := by
  change Tree.branch (159 : Fin 170) _ = Tree.branch (159 : Fin 170) _
  apply congrArg (Tree.branch (159 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0534

def B0532 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0533, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0532 : B0532.tree = HexagonCover.N7900.SplitData.node0532 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0533
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0531 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0532, Tip0479_0538, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0531 : B0531.tree = HexagonCover.N7900.SplitData.node0531 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0532
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0530 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0531]
theorem treeEq0530 : B0530.tree = HexagonCover.N7900.SplitData.node0530 := by
  change Tree.branch (132 : Fin 170) _ = Tree.branch (132 : Fin 170) _
  apply congrArg (Tree.branch (132 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0531

def B0529 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0530]
theorem treeEq0529 : B0529.tree = HexagonCover.N7900.SplitData.node0529 := by
  change Tree.branch (133 : Fin 170) _ = Tree.branch (133 : Fin 170) _
  apply congrArg (Tree.branch (133 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530

def B0528 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0529, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0528 : B0528.tree = HexagonCover.N7900.SplitData.node0528 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0529
  · rfl
  · rfl

def B0527 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0528, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0527 : B0527.tree = HexagonCover.N7900.SplitData.node0527 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl

def B0526 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0527]
theorem treeEq0526 : B0526.tree = HexagonCover.N7900.SplitData.node0526 := by
  change Tree.branch (124 : Fin 170) _ = Tree.branch (124 : Fin 170) _
  apply congrArg (Tree.branch (124 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0527

def B0569 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0569 : B0569.tree = HexagonCover.N7900.SplitData.node0569 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0568 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0569, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0568 : B0568.tree = HexagonCover.N7900.SplitData.node0568 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0569
  · rfl
  · rfl

def B0567 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0568, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0567 : B0567.tree = HexagonCover.N7900.SplitData.node0567 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0568
  · rfl

def B0525 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0526, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0567]
theorem treeEq0525 : B0525.tree = HexagonCover.N7900.SplitData.node0525 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0567

def B0479 : Block := .branch 74 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip0479_0480, B0525, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0479 : B0479.tree = HexagonCover.N7900.SplitData.node0479 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0525
  · rfl
  · rfl
  · rfl

theorem accepted0479 : B0479.accepted = true := by decide +kernel
theorem checked0479 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0479 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0479]
  exact B0479.sound accepted0479
#print axioms checked0479

def B0684 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0684 : B0684.tree = HexagonCover.N7900.SplitData.node0684 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0683 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0684]
theorem treeEq0683 : B0683.tree = HexagonCover.N7900.SplitData.node0683 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0684

def B0682 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0683, (.leaf 0 [] 0)]
theorem treeEq0682 : B0682.tree = HexagonCover.N7900.SplitData.node0682 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0683
  · rfl

def B0681 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0682, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0681 : B0681.tree = HexagonCover.N7900.SplitData.node0681 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0682
  · rfl

def B0680 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0681, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0680 : B0680.tree = HexagonCover.N7900.SplitData.node0680 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0681
  · rfl
  · rfl

def B0679 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0680, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0679 : B0679.tree = HexagonCover.N7900.SplitData.node0679 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0680
  · rfl

def B0688 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0688 : B0688.tree = HexagonCover.N7900.SplitData.node0688 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0687 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0688, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0687 : B0687.tree = HexagonCover.N7900.SplitData.node0687 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0688
  · rfl

def B0686 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0687, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0686 : B0686.tree = HexagonCover.N7900.SplitData.node0686 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0687
  · rfl
  · rfl

def B0685 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0686]
theorem treeEq0685 : B0685.tree = HexagonCover.N7900.SplitData.node0685 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0686

def B0678 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0679, B0685, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0678 : B0678.tree = HexagonCover.N7900.SplitData.node0678 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0679
  · exact treeEq0685
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0690 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0690 : B0690.tree = HexagonCover.N7900.SplitData.node0690 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0689 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0690, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0689 : B0689.tree = HexagonCover.N7900.SplitData.node0689 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690
  · rfl
  · rfl

def B0677 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0678, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0689]
theorem treeEq0677 : B0677.tree = HexagonCover.N7900.SplitData.node0677 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0678
  · rfl
  · rfl
  · rfl
  · exact treeEq0689

theorem accepted0677 : B0677.accepted = true := by decide +kernel
theorem checked0677 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0677 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0677]
  exact B0677.sound accepted0677
#print axioms checked0677

def Tip0676_0677 : Block := .tip HexagonCover.N7900.SplitData.node0677 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0677
def B0698 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0698 : B0698.tree = HexagonCover.N7900.SplitData.node0698 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0697 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0698]
theorem treeEq0697 : B0697.tree = HexagonCover.N7900.SplitData.node0697 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0698

def B0696 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0697, (.leaf 0 [] 0)]
theorem treeEq0696 : B0696.tree = HexagonCover.N7900.SplitData.node0696 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0697
  · rfl

def B0695 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0696, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0695 : B0695.tree = HexagonCover.N7900.SplitData.node0695 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0696
  · rfl

def B0694 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0695, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0694 : B0694.tree = HexagonCover.N7900.SplitData.node0694 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0695
  · rfl
  · rfl

def B0693 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0694, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0693 : B0693.tree = HexagonCover.N7900.SplitData.node0693 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0694
  · rfl

def B0702 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0702 : B0702.tree = HexagonCover.N7900.SplitData.node0702 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0701 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0702, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0701 : B0701.tree = HexagonCover.N7900.SplitData.node0701 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0702
  · rfl

def B0700 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0701, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0700 : B0700.tree = HexagonCover.N7900.SplitData.node0700 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0701
  · rfl
  · rfl

def B0699 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38687987410909568413229064, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0700]
theorem treeEq0699 : B0699.tree = HexagonCover.N7900.SplitData.node0699 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0700

def B0692 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0693, B0699, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0692 : B0692.tree = HexagonCover.N7900.SplitData.node0692 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0693
  · exact treeEq0699
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0704 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0704 : B0704.tree = HexagonCover.N7900.SplitData.node0704 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0703 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 505).pointIds 505), B0704, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0703 : B0703.tree = HexagonCover.N7900.SplitData.node0703 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0704
  · rfl
  · rfl

def B0691 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0692, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0703]
theorem treeEq0691 : B0691.tree = HexagonCover.N7900.SplitData.node0691 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0692
  · rfl
  · rfl
  · rfl
  · exact treeEq0703

def B0676 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0676_0677, B0691, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0676 : B0676.tree = HexagonCover.N7900.SplitData.node0676 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0691
  · rfl
  · rfl
  · rfl

theorem accepted0676 : B0676.accepted = true := by decide +kernel
theorem checked0676 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0676 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0676]
  exact B0676.sound accepted0676
#print axioms checked0676

end HexagonCover.N7900.SplitAlignedTree.Run0007
