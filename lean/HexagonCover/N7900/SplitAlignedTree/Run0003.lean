import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0003
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B0317 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0317 : B0317.tree = HexagonCover.N7900.SplitData.node0317 := by
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

def B0316 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0317]
theorem treeEq0316 : B0316.tree = HexagonCover.N7900.SplitData.node0316 := by
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
  · exact treeEq0317

def B0315 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0316, (.leaf 0 [] 0)]
theorem treeEq0315 : B0315.tree = HexagonCover.N7900.SplitData.node0315 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0316
  · rfl

def B0314 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0315, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0314 : B0314.tree = HexagonCover.N7900.SplitData.node0314 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · rfl

def B0313 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0314, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0313 : B0313.tree = HexagonCover.N7900.SplitData.node0313 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0314
  · rfl
  · rfl

def B0312 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0313, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0312 : B0312.tree = HexagonCover.N7900.SplitData.node0312 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0313
  · rfl

def B0321 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0321 : B0321.tree = HexagonCover.N7900.SplitData.node0321 := by
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

def B0320 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0321, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0320 : B0320.tree = HexagonCover.N7900.SplitData.node0320 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl

def B0319 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0320, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0319 : B0319.tree = HexagonCover.N7900.SplitData.node0319 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0320
  · rfl
  · rfl

def B0318 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0319]
theorem treeEq0318 : B0318.tree = HexagonCover.N7900.SplitData.node0318 := by
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
  · exact treeEq0319

def B0311 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0312, B0318, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0311 : B0311.tree = HexagonCover.N7900.SplitData.node0311 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0312
  · exact treeEq0318
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0323 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0323 : B0323.tree = HexagonCover.N7900.SplitData.node0323 := by
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

def B0322 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0323, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0322 : B0322.tree = HexagonCover.N7900.SplitData.node0322 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0323
  · rfl
  · rfl

def B0310 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0311, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0322]
theorem treeEq0310 : B0310.tree = HexagonCover.N7900.SplitData.node0310 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0311
  · rfl
  · rfl
  · rfl
  · exact treeEq0322

theorem accepted0310 : B0310.accepted = true := by decide +kernel
theorem checked0310 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0310 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0310]
  exact B0310.sound accepted0310
#print axioms checked0310

def Tip0309_0310 : Block := .tip HexagonCover.N7900.SplitData.node0310 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0310
def B0331 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0331 : B0331.tree = HexagonCover.N7900.SplitData.node0331 := by
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

def B0330 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0331]
theorem treeEq0330 : B0330.tree = HexagonCover.N7900.SplitData.node0330 := by
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
  · exact treeEq0331

def B0329 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0330, (.leaf 0 [] 0)]
theorem treeEq0329 : B0329.tree = HexagonCover.N7900.SplitData.node0329 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl

def B0328 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0329, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0328 : B0328.tree = HexagonCover.N7900.SplitData.node0328 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329
  · rfl

def B0327 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0328, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0327 : B0327.tree = HexagonCover.N7900.SplitData.node0327 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0328
  · rfl
  · rfl

def B0326 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0327, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0326 : B0326.tree = HexagonCover.N7900.SplitData.node0326 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0327
  · rfl

def B0335 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0335 : B0335.tree = HexagonCover.N7900.SplitData.node0335 := by
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

def B0334 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0335, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0334 : B0334.tree = HexagonCover.N7900.SplitData.node0334 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl

def B0333 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0334, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0333 : B0333.tree = HexagonCover.N7900.SplitData.node0333 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl
  · rfl

def B0332 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0333]
theorem treeEq0332 : B0332.tree = HexagonCover.N7900.SplitData.node0332 := by
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
  · exact treeEq0333

def B0325 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0326, B0332, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0325 : B0325.tree = HexagonCover.N7900.SplitData.node0325 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0326
  · exact treeEq0332
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0337 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0337 : B0337.tree = HexagonCover.N7900.SplitData.node0337 := by
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

def B0336 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0337, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0336 : B0336.tree = HexagonCover.N7900.SplitData.node0336 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl
  · rfl

def B0324 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0325, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0336]
theorem treeEq0324 : B0324.tree = HexagonCover.N7900.SplitData.node0324 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0325
  · rfl
  · rfl
  · rfl
  · exact treeEq0336

def B0309 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0309_0310, B0324, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0309 : B0309.tree = HexagonCover.N7900.SplitData.node0309 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · rfl
  · rfl

theorem accepted0309 : B0309.accepted = true := by decide +kernel
theorem checked0309 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0309 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0309]
  exact B0309.sound accepted0309
#print axioms checked0309

def B0362 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0362 : B0362.tree = HexagonCover.N7900.SplitData.node0362 := by
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

def B0361 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0362]
theorem treeEq0361 : B0361.tree = HexagonCover.N7900.SplitData.node0361 := by
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
  · exact treeEq0362

def B0360 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0361, (.leaf 0 [] 0)]
theorem treeEq0360 : B0360.tree = HexagonCover.N7900.SplitData.node0360 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0361
  · rfl

def B0359 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0360, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0359 : B0359.tree = HexagonCover.N7900.SplitData.node0359 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0360
  · rfl

def B0358 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0359, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0358 : B0358.tree = HexagonCover.N7900.SplitData.node0358 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0359
  · rfl
  · rfl

def B0357 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0358, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0357 : B0357.tree = HexagonCover.N7900.SplitData.node0357 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0358
  · rfl

def B0366 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0366 : B0366.tree = HexagonCover.N7900.SplitData.node0366 := by
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

def B0365 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0366, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0365 : B0365.tree = HexagonCover.N7900.SplitData.node0365 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0366
  · rfl

def B0364 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0365, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0364 : B0364.tree = HexagonCover.N7900.SplitData.node0364 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl
  · rfl

def B0363 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0364]
theorem treeEq0363 : B0363.tree = HexagonCover.N7900.SplitData.node0363 := by
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
  · exact treeEq0364

def B0356 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0357, B0363, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0356 : B0356.tree = HexagonCover.N7900.SplitData.node0356 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0357
  · exact treeEq0363
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0368 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0368 : B0368.tree = HexagonCover.N7900.SplitData.node0368 := by
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

def B0367 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0368, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0367 : B0367.tree = HexagonCover.N7900.SplitData.node0367 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0368
  · rfl
  · rfl

def B0355 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0356, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0367]
theorem treeEq0355 : B0355.tree = HexagonCover.N7900.SplitData.node0355 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0356
  · rfl
  · rfl
  · rfl
  · exact treeEq0367

theorem accepted0355 : B0355.accepted = true := by decide +kernel
theorem checked0355 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0355 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0355]
  exact B0355.sound accepted0355
#print axioms checked0355

def Tip0354_0355 : Block := .tip HexagonCover.N7900.SplitData.node0355 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0355
def B0376 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0376 : B0376.tree = HexagonCover.N7900.SplitData.node0376 := by
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

def B0375 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0376]
theorem treeEq0375 : B0375.tree = HexagonCover.N7900.SplitData.node0375 := by
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
  · exact treeEq0376

def B0374 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0375, (.leaf 0 [] 0)]
theorem treeEq0374 : B0374.tree = HexagonCover.N7900.SplitData.node0374 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375
  · rfl

def B0373 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0374, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0373 : B0373.tree = HexagonCover.N7900.SplitData.node0373 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0374
  · rfl

def B0372 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0373, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0372 : B0372.tree = HexagonCover.N7900.SplitData.node0372 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl
  · rfl

def B0371 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0372, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0371 : B0371.tree = HexagonCover.N7900.SplitData.node0371 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0372
  · rfl

def B0380 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0380 : B0380.tree = HexagonCover.N7900.SplitData.node0380 := by
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

def B0379 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0380, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0379 : B0379.tree = HexagonCover.N7900.SplitData.node0379 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0380
  · rfl

def B0378 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0379, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0378 : B0378.tree = HexagonCover.N7900.SplitData.node0378 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0379
  · rfl
  · rfl

def B0377 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38690348594151003235835912, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0378]
theorem treeEq0377 : B0377.tree = HexagonCover.N7900.SplitData.node0377 := by
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
  · exact treeEq0378

def B0370 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0371, B0377, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0370 : B0370.tree = HexagonCover.N7900.SplitData.node0370 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0371
  · exact treeEq0377
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0382 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0382 : B0382.tree = HexagonCover.N7900.SplitData.node0382 := by
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

def B0381 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 504).pointIds 504), B0382, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0381 : B0381.tree = HexagonCover.N7900.SplitData.node0381 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl
  · rfl

def B0369 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0370, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0381]
theorem treeEq0369 : B0369.tree = HexagonCover.N7900.SplitData.node0369 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0370
  · rfl
  · rfl
  · rfl
  · exact treeEq0381

def B0354 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0354_0355, B0369, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0354 : B0354.tree = HexagonCover.N7900.SplitData.node0354 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0369
  · rfl
  · rfl
  · rfl

theorem accepted0354 : B0354.accepted = true := by decide +kernel
theorem checked0354 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0354 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0354]
  exact B0354.sound accepted0354
#print axioms checked0354

def Tip0296_0309 : Block := .tip HexagonCover.N7900.SplitData.node0309 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0309
def B0308 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0308 : B0308.tree = HexagonCover.N7900.SplitData.node0308 := by
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

def B0307 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0308, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0307 : B0307.tree = HexagonCover.N7900.SplitData.node0307 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0308
  · rfl
  · rfl

def B0306 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0307, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0306 : B0306.tree = HexagonCover.N7900.SplitData.node0306 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0307
  · rfl

def B0305 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0306]
theorem treeEq0305 : B0305.tree = HexagonCover.N7900.SplitData.node0305 := by
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
  · exact treeEq0306

def B0304 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0305]
theorem treeEq0304 : B0304.tree = HexagonCover.N7900.SplitData.node0304 := by
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
  · exact treeEq0305

def B0303 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0304, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0303 : B0303.tree = HexagonCover.N7900.SplitData.node0303 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0304
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0302 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0303, Tip0296_0309, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0302 : B0302.tree = HexagonCover.N7900.SplitData.node0302 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0303
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0301 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0302]
theorem treeEq0301 : B0301.tree = HexagonCover.N7900.SplitData.node0301 := by
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
  · exact treeEq0302

def B0300 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0301]
theorem treeEq0300 : B0300.tree = HexagonCover.N7900.SplitData.node0300 := by
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
  · exact treeEq0301

def B0299 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0300, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0299 : B0299.tree = HexagonCover.N7900.SplitData.node0299 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0300
  · rfl
  · rfl

def B0298 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0299, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0298 : B0298.tree = HexagonCover.N7900.SplitData.node0298 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0299
  · rfl

def B0297 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0298]
theorem treeEq0297 : B0297.tree = HexagonCover.N7900.SplitData.node0297 := by
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
  · exact treeEq0298

def B0340 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0340 : B0340.tree = HexagonCover.N7900.SplitData.node0340 := by
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

def B0339 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0340, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0339 : B0339.tree = HexagonCover.N7900.SplitData.node0339 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0340
  · rfl
  · rfl

def B0338 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0339, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0338 : B0338.tree = HexagonCover.N7900.SplitData.node0338 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0339
  · rfl

def B0296 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0297, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0338]
theorem treeEq0296 : B0296.tree = HexagonCover.N7900.SplitData.node0296 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0297
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0338

theorem accepted0296 : B0296.accepted = true := by decide +kernel
theorem checked0296 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0296 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0296]
  exact B0296.sound accepted0296
#print axioms checked0296

end HexagonCover.N7900.SplitAlignedTree.Run0003
