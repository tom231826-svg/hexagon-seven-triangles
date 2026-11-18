import HexagonCover.N7900.SplitAlignedTree.Run0000
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0001
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0125_0126 : Block := .tip HexagonCover.N7900.SplitData.node0126 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0000.checked0126
def B0148 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0148 : B0148.tree = HexagonCover.N7900.SplitData.node0148 := by
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

def B0147 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0148]
theorem treeEq0147 : B0147.tree = HexagonCover.N7900.SplitData.node0147 := by
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
  · exact treeEq0148

def B0146 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0147, (.leaf 0 [] 0)]
theorem treeEq0146 : B0146.tree = HexagonCover.N7900.SplitData.node0146 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0147
  · rfl

def B0145 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0146, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0145 : B0145.tree = HexagonCover.N7900.SplitData.node0145 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0146
  · rfl

def B0144 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0145, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0144 : B0144.tree = HexagonCover.N7900.SplitData.node0144 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0145
  · rfl
  · rfl

def B0143 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0144, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0143 : B0143.tree = HexagonCover.N7900.SplitData.node0143 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0144
  · rfl

def B0152 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0152 : B0152.tree = HexagonCover.N7900.SplitData.node0152 := by
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

def B0151 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0152, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0151 : B0151.tree = HexagonCover.N7900.SplitData.node0151 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl

def B0150 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38723405159531090752331784, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 487).pointIds 487), B0151, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0150 : B0150.tree = HexagonCover.N7900.SplitData.node0150 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0151
  · rfl
  · rfl

def B0149 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38723405159531090752331784, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0150]
theorem treeEq0149 : B0149.tree = HexagonCover.N7900.SplitData.node0149 := by
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
  · exact treeEq0150

def B0142 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38723405159531090752331784, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0143, B0149, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0142 : B0142.tree = HexagonCover.N7900.SplitData.node0142 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0143
  · exact treeEq0149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0154 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0154 : B0154.tree = HexagonCover.N7900.SplitData.node0154 := by
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

def B0153 : Block := .branch 162 ![385, 1538, 6148, 37778931862957161734152, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 487).pointIds 487), B0154, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0153 : B0153.tree = HexagonCover.N7900.SplitData.node0153 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · rfl
  · rfl

def B0141 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38723405159531090752331784, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0142, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0153]
theorem treeEq0141 : B0141.tree = HexagonCover.N7900.SplitData.node0141 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0142
  · rfl
  · rfl
  · rfl
  · exact treeEq0153

def B0125 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0125_0126, B0141, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0125 : B0125.tree = HexagonCover.N7900.SplitData.node0125 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0141
  · rfl
  · rfl
  · rfl

theorem accepted0125 : B0125.accepted = true := by decide +kernel
theorem checked0125 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0125 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0125]
  exact B0125.sound accepted0125
#print axioms checked0125

def B0179 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0179 : B0179.tree = HexagonCover.N7900.SplitData.node0179 := by
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

def B0178 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0179]
theorem treeEq0178 : B0178.tree = HexagonCover.N7900.SplitData.node0178 := by
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
  · exact treeEq0179

def B0177 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0178, (.leaf 0 [] 0)]
theorem treeEq0177 : B0177.tree = HexagonCover.N7900.SplitData.node0177 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0178
  · rfl

def B0176 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0177, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0176 : B0176.tree = HexagonCover.N7900.SplitData.node0176 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0177
  · rfl

def B0175 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0176, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0175 : B0175.tree = HexagonCover.N7900.SplitData.node0175 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0176
  · rfl
  · rfl

def B0174 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0175, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0174 : B0174.tree = HexagonCover.N7900.SplitData.node0174 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0175
  · rfl

def B0183 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0183 : B0183.tree = HexagonCover.N7900.SplitData.node0183 := by
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

def B0182 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0183, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0182 : B0182.tree = HexagonCover.N7900.SplitData.node0182 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0183
  · rfl

def B0181 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38704515693599612171477000, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 502).pointIds 502), B0182, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0181 : B0181.tree = HexagonCover.N7900.SplitData.node0181 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0182
  · rfl
  · rfl

def B0180 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38704515693599612171477000, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0181]
theorem treeEq0180 : B0180.tree = HexagonCover.N7900.SplitData.node0180 := by
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
  · exact treeEq0181

def B0173 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0174, B0180, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0173 : B0173.tree = HexagonCover.N7900.SplitData.node0173 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0174
  · exact treeEq0180
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0185 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0185 : B0185.tree = HexagonCover.N7900.SplitData.node0185 := by
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

def B0184 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 502).pointIds 502), B0185, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0184 : B0184.tree = HexagonCover.N7900.SplitData.node0184 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0185
  · rfl
  · rfl

def B0172 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0173, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0184]
theorem treeEq0172 : B0172.tree = HexagonCover.N7900.SplitData.node0172 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0173
  · rfl
  · rfl
  · rfl
  · exact treeEq0184

theorem accepted0172 : B0172.accepted = true := by decide +kernel
theorem checked0172 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0172 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0172]
  exact B0172.sound accepted0172
#print axioms checked0172

def Tip0171_0172 : Block := .tip HexagonCover.N7900.SplitData.node0172 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0172
def B0193 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0193 : B0193.tree = HexagonCover.N7900.SplitData.node0193 := by
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

def B0192 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0193]
theorem treeEq0192 : B0192.tree = HexagonCover.N7900.SplitData.node0192 := by
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
  · exact treeEq0193

def B0191 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0192, (.leaf 0 [] 0)]
theorem treeEq0191 : B0191.tree = HexagonCover.N7900.SplitData.node0191 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0192
  · rfl

def B0190 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0191, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0190 : B0190.tree = HexagonCover.N7900.SplitData.node0190 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl

def B0189 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0190, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0189 : B0189.tree = HexagonCover.N7900.SplitData.node0189 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0190
  · rfl
  · rfl

def B0188 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0189, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0188 : B0188.tree = HexagonCover.N7900.SplitData.node0188 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0189
  · rfl

def B0197 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0197 : B0197.tree = HexagonCover.N7900.SplitData.node0197 := by
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

def B0196 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0197, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0196 : B0196.tree = HexagonCover.N7900.SplitData.node0196 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197
  · rfl

def B0195 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38704515693599612171477000, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 502).pointIds 502), B0196, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0195 : B0195.tree = HexagonCover.N7900.SplitData.node0195 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0196
  · rfl
  · rfl

def B0194 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38704515693599612171477000, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0195]
theorem treeEq0194 : B0194.tree = HexagonCover.N7900.SplitData.node0194 := by
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
  · exact treeEq0195

def B0187 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0188, B0194, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0187 : B0187.tree = HexagonCover.N7900.SplitData.node0187 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0188
  · exact treeEq0194
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0199 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0199 : B0199.tree = HexagonCover.N7900.SplitData.node0199 := by
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

def B0198 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 502).pointIds 502), B0199, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0198 : B0198.tree = HexagonCover.N7900.SplitData.node0198 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl

def B0186 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0187, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0198]
theorem treeEq0186 : B0186.tree = HexagonCover.N7900.SplitData.node0186 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0187
  · rfl
  · rfl
  · rfl
  · exact treeEq0198

def B0171 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0171_0172, B0186, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0171 : B0171.tree = HexagonCover.N7900.SplitData.node0171 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl
  · rfl
  · rfl

theorem accepted0171 : B0171.accepted = true := by decide +kernel
theorem checked0171 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0171 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0171]
  exact B0171.sound accepted0171
#print axioms checked0171

def Tip0112_0125 : Block := .tip HexagonCover.N7900.SplitData.node0125 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] checked0125
def B0124 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0124 : B0124.tree = HexagonCover.N7900.SplitData.node0124 := by
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

def B0123 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0124, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0123 : B0123.tree = HexagonCover.N7900.SplitData.node0123 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0124
  · rfl
  · rfl

def B0122 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0123, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0122 : B0122.tree = HexagonCover.N7900.SplitData.node0122 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0123
  · rfl

def B0121 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0122]
theorem treeEq0121 : B0121.tree = HexagonCover.N7900.SplitData.node0121 := by
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
  · exact treeEq0122

def B0120 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0121]
theorem treeEq0120 : B0120.tree = HexagonCover.N7900.SplitData.node0120 := by
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
  · exact treeEq0121

def B0119 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0120, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0119 : B0119.tree = HexagonCover.N7900.SplitData.node0119 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0120
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0118 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] ![B0119, Tip0112_0125, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0118 : B0118.tree = HexagonCover.N7900.SplitData.node0118 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0119
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0117 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0118]
theorem treeEq0117 : B0117.tree = HexagonCover.N7900.SplitData.node0117 := by
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
  · exact treeEq0118

def B0116 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0117]
theorem treeEq0116 : B0116.tree = HexagonCover.N7900.SplitData.node0116 := by
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
  · exact treeEq0117

def B0115 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0116, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0115 : B0115.tree = HexagonCover.N7900.SplitData.node0115 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0116
  · rfl
  · rfl

def B0114 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0115, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0114 : B0114.tree = HexagonCover.N7900.SplitData.node0114 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0115
  · rfl

def B0113 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0114]
theorem treeEq0113 : B0113.tree = HexagonCover.N7900.SplitData.node0113 := by
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
  · exact treeEq0114

def B0157 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0157 : B0157.tree = HexagonCover.N7900.SplitData.node0157 := by
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

def B0156 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0157, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0156 : B0156.tree = HexagonCover.N7900.SplitData.node0156 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0157
  · rfl
  · rfl

def B0155 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0156, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0155 : B0155.tree = HexagonCover.N7900.SplitData.node0155 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0156
  · rfl

def B0112 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0113, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0155]
theorem treeEq0112 : B0112.tree = HexagonCover.N7900.SplitData.node0112 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0113
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0155

theorem accepted0112 : B0112.accepted = true := by decide +kernel
theorem checked0112 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0112 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0112]
  exact B0112.sound accepted0112
#print axioms checked0112

def B0225 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0225 : B0225.tree = HexagonCover.N7900.SplitData.node0225 := by
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

def B0224 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0225]
theorem treeEq0224 : B0224.tree = HexagonCover.N7900.SplitData.node0224 := by
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
  · exact treeEq0225

def B0223 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0224, (.leaf 0 [] 0)]
theorem treeEq0223 : B0223.tree = HexagonCover.N7900.SplitData.node0223 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl

def B0222 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0223, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0222 : B0222.tree = HexagonCover.N7900.SplitData.node0222 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0223
  · rfl

def B0221 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0222, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0221 : B0221.tree = HexagonCover.N7900.SplitData.node0221 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0222
  · rfl
  · rfl

def B0220 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0221, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0220 : B0220.tree = HexagonCover.N7900.SplitData.node0220 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0221
  · rfl

def B0229 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0229 : B0229.tree = HexagonCover.N7900.SplitData.node0229 := by
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

def B0228 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0229, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0228 : B0228.tree = HexagonCover.N7900.SplitData.node0228 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0229
  · rfl

def B0227 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0228, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0227 : B0227.tree = HexagonCover.N7900.SplitData.node0227 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl
  · rfl

def B0226 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0227]
theorem treeEq0226 : B0226.tree = HexagonCover.N7900.SplitData.node0226 := by
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
  · exact treeEq0227

def B0219 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0220, B0226, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0219 : B0219.tree = HexagonCover.N7900.SplitData.node0219 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0220
  · exact treeEq0226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0231 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0231 : B0231.tree = HexagonCover.N7900.SplitData.node0231 := by
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

def B0230 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0231, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0230 : B0230.tree = HexagonCover.N7900.SplitData.node0230 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231
  · rfl
  · rfl

def B0218 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0219, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0230]
theorem treeEq0218 : B0218.tree = HexagonCover.N7900.SplitData.node0218 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0219
  · rfl
  · rfl
  · rfl
  · exact treeEq0230

theorem accepted0218 : B0218.accepted = true := by decide +kernel
theorem checked0218 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0218 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0218]
  exact B0218.sound accepted0218
#print axioms checked0218

end HexagonCover.N7900.SplitAlignedTree.Run0001
