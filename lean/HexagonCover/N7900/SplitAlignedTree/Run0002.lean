import HexagonCover.N7900.SplitAlignedTree.Run0001
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0002
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0217_0218 : Block := .tip HexagonCover.N7900.SplitData.node0218 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0001.checked0218
def B0239 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0239 : B0239.tree = HexagonCover.N7900.SplitData.node0239 := by
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

def B0238 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0239]
theorem treeEq0238 : B0238.tree = HexagonCover.N7900.SplitData.node0238 := by
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
  · exact treeEq0239

def B0237 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0238, (.leaf 0 [] 0)]
theorem treeEq0237 : B0237.tree = HexagonCover.N7900.SplitData.node0237 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238
  · rfl

def B0236 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0237, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0236 : B0236.tree = HexagonCover.N7900.SplitData.node0236 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0237
  · rfl

def B0235 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0236, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0235 : B0235.tree = HexagonCover.N7900.SplitData.node0235 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0236
  · rfl
  · rfl

def B0234 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0235, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0234 : B0234.tree = HexagonCover.N7900.SplitData.node0234 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0235
  · rfl

def B0243 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0243 : B0243.tree = HexagonCover.N7900.SplitData.node0243 := by
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

def B0242 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0243, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0242 : B0242.tree = HexagonCover.N7900.SplitData.node0242 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243
  · rfl

def B0241 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0242, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0241 : B0241.tree = HexagonCover.N7900.SplitData.node0241 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0242
  · rfl
  · rfl

def B0240 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0241]
theorem treeEq0240 : B0240.tree = HexagonCover.N7900.SplitData.node0240 := by
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
  · exact treeEq0241

def B0233 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0234, B0240, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0233 : B0233.tree = HexagonCover.N7900.SplitData.node0233 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0234
  · exact treeEq0240
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0245 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0245 : B0245.tree = HexagonCover.N7900.SplitData.node0245 := by
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

def B0244 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0245, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0244 : B0244.tree = HexagonCover.N7900.SplitData.node0244 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245
  · rfl
  · rfl

def B0232 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0233, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0244]
theorem treeEq0232 : B0232.tree = HexagonCover.N7900.SplitData.node0232 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0233
  · rfl
  · rfl
  · rfl
  · exact treeEq0244

def B0217 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0217_0218, B0232, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0217 : B0217.tree = HexagonCover.N7900.SplitData.node0217 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl
  · rfl
  · rfl

theorem accepted0217 : B0217.accepted = true := by decide +kernel
theorem checked0217 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0217 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0217]
  exact B0217.sound accepted0217
#print axioms checked0217

def B0270 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0270 : B0270.tree = HexagonCover.N7900.SplitData.node0270 := by
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

def B0269 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0270]
theorem treeEq0269 : B0269.tree = HexagonCover.N7900.SplitData.node0269 := by
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
  · exact treeEq0270

def B0268 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0269, (.leaf 0 [] 0)]
theorem treeEq0268 : B0268.tree = HexagonCover.N7900.SplitData.node0268 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0269
  · rfl

def B0267 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0268, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0267 : B0267.tree = HexagonCover.N7900.SplitData.node0267 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0268
  · rfl

def B0266 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0267, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0266 : B0266.tree = HexagonCover.N7900.SplitData.node0266 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267
  · rfl
  · rfl

def B0265 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0266, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0265 : B0265.tree = HexagonCover.N7900.SplitData.node0265 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0266
  · rfl

def B0274 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0274 : B0274.tree = HexagonCover.N7900.SplitData.node0274 := by
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

def B0273 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0274, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0273 : B0273.tree = HexagonCover.N7900.SplitData.node0273 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0274
  · rfl

def B0272 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0273, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0272 : B0272.tree = HexagonCover.N7900.SplitData.node0272 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0273
  · rfl
  · rfl

def B0271 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0272]
theorem treeEq0271 : B0271.tree = HexagonCover.N7900.SplitData.node0271 := by
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
  · exact treeEq0272

def B0264 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0265, B0271, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0264 : B0264.tree = HexagonCover.N7900.SplitData.node0264 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0265
  · exact treeEq0271
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0276 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0276 : B0276.tree = HexagonCover.N7900.SplitData.node0276 := by
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

def B0275 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0276, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0275 : B0275.tree = HexagonCover.N7900.SplitData.node0275 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl
  · rfl

def B0263 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0264, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0275]
theorem treeEq0263 : B0263.tree = HexagonCover.N7900.SplitData.node0263 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0264
  · rfl
  · rfl
  · rfl
  · exact treeEq0275

theorem accepted0263 : B0263.accepted = true := by decide +kernel
theorem checked0263 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0263 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0263]
  exact B0263.sound accepted0263
#print axioms checked0263

def Tip0262_0263 : Block := .tip HexagonCover.N7900.SplitData.node0263 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0263
def B0284 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0284 : B0284.tree = HexagonCover.N7900.SplitData.node0284 := by
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

def B0283 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0284]
theorem treeEq0283 : B0283.tree = HexagonCover.N7900.SplitData.node0283 := by
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
  · exact treeEq0284

def B0282 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0283, (.leaf 0 [] 0)]
theorem treeEq0282 : B0282.tree = HexagonCover.N7900.SplitData.node0282 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283
  · rfl

def B0281 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0282, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0281 : B0281.tree = HexagonCover.N7900.SplitData.node0281 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl

def B0280 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0281, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0280 : B0280.tree = HexagonCover.N7900.SplitData.node0280 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0281
  · rfl
  · rfl

def B0279 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0280, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0279 : B0279.tree = HexagonCover.N7900.SplitData.node0279 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280
  · rfl

def B0288 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0288 : B0288.tree = HexagonCover.N7900.SplitData.node0288 := by
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

def B0287 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 5846006549323611672814739330865132078623730270224, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 489).pointIds 489), B0288, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0287 : B0287.tree = HexagonCover.N7900.SplitData.node0287 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0288
  · rfl

def B0286 : Block := .branch 162 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0287, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 488).pointIds 488)]
theorem treeEq0286 : B0286.tree = HexagonCover.N7900.SplitData.node0286 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0287
  · rfl
  · rfl

def B0285 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38695070960633872881049608, 98320, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0286]
theorem treeEq0285 : B0285.tree = HexagonCover.N7900.SplitData.node0285 := by
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
  · exact treeEq0286

def B0278 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0279, B0285, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0278 : B0278.tree = HexagonCover.N7900.SplitData.node0278 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0279
  · exact treeEq0285
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0290 : Block := .branch 142 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 495).pointIds 495), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0290 : B0290.tree = HexagonCover.N7900.SplitData.node0290 := by
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

def B0289 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 98320, 393248, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 503).pointIds 503), B0290, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 490).pointIds 490)]
theorem treeEq0289 : B0289.tree = HexagonCover.N7900.SplitData.node0289 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0290
  · rfl
  · rfl

def B0277 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0278, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0289]
theorem treeEq0277 : B0277.tree = HexagonCover.N7900.SplitData.node0277 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0278
  · rfl
  · rfl
  · rfl
  · exact treeEq0289

def B0262 : Block := .branch 75 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0262_0263, B0277, (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0262 : B0262.tree = HexagonCover.N7900.SplitData.node0262 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0277
  · rfl
  · rfl
  · rfl

theorem accepted0262 : B0262.accepted = true := by decide +kernel
theorem checked0262 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0262 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0262]
  exact B0262.sound accepted0262
#print axioms checked0262

def Tip0204_0217 : Block := .tip HexagonCover.N7900.SplitData.node0217 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] checked0217
def B0216 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0216 : B0216.tree = HexagonCover.N7900.SplitData.node0216 := by
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

def B0215 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0216, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0215 : B0215.tree = HexagonCover.N7900.SplitData.node0215 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl
  · rfl

def B0214 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0215, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0214 : B0214.tree = HexagonCover.N7900.SplitData.node0214 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215
  · rfl

def B0213 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0214]
theorem treeEq0213 : B0213.tree = HexagonCover.N7900.SplitData.node0213 := by
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
  · exact treeEq0214

def B0212 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0213]
theorem treeEq0212 : B0212.tree = HexagonCover.N7900.SplitData.node0212 := by
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
  · exact treeEq0213

def B0211 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0212, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0211 : B0211.tree = HexagonCover.N7900.SplitData.node0211 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0212
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0210 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38695070960633872881049608, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0211, Tip0204_0217, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0210 : B0210.tree = HexagonCover.N7900.SplitData.node0210 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0211
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0209 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38695070960633872881049608, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0210]
theorem treeEq0209 : B0209.tree = HexagonCover.N7900.SplitData.node0209 := by
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
  · exact treeEq0210

def B0208 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38695070960633872881049608, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0209]
theorem treeEq0208 : B0208.tree = HexagonCover.N7900.SplitData.node0208 := by
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
  · exact treeEq0209

def B0207 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0208, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0207 : B0207.tree = HexagonCover.N7900.SplitData.node0207 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0208
  · rfl
  · rfl

def B0206 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0207, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0206 : B0206.tree = HexagonCover.N7900.SplitData.node0206 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207
  · rfl

def B0205 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0206]
theorem treeEq0205 : B0205.tree = HexagonCover.N7900.SplitData.node0205 := by
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
  · exact treeEq0206

def B0248 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0248 : B0248.tree = HexagonCover.N7900.SplitData.node0248 := by
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

def B0247 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0248, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0247 : B0247.tree = HexagonCover.N7900.SplitData.node0247 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0248
  · rfl
  · rfl

def B0246 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0247, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0246 : B0246.tree = HexagonCover.N7900.SplitData.node0246 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl

def B0204 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0205, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0246]
theorem treeEq0204 : B0204.tree = HexagonCover.N7900.SplitData.node0204 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0205
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0246

theorem accepted0204 : B0204.accepted = true := by decide +kernel
theorem checked0204 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0204 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0204]
  exact B0204.sound accepted0204
#print axioms checked0204

def Tip0111_0171 : Block := .tip HexagonCover.N7900.SplitData.node0171 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0001.checked0171
def Tip0111_0112 : Block := .tip HexagonCover.N7900.SplitData.node0112 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0001.checked0112
def B0170 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0170 : B0170.tree = HexagonCover.N7900.SplitData.node0170 := by
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

def B0169 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0170, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0169 : B0169.tree = HexagonCover.N7900.SplitData.node0169 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0170
  · rfl
  · rfl

def B0168 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0169, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0168 : B0168.tree = HexagonCover.N7900.SplitData.node0168 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0169
  · rfl

def B0167 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0168]
theorem treeEq0167 : B0167.tree = HexagonCover.N7900.SplitData.node0167 := by
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
  · exact treeEq0168

def B0166 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0167]
theorem treeEq0166 : B0166.tree = HexagonCover.N7900.SplitData.node0166 := by
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
  · exact treeEq0167

def B0165 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0166, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0165 : B0165.tree = HexagonCover.N7900.SplitData.node0165 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0166
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0164 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0165, Tip0111_0171, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0164 : B0164.tree = HexagonCover.N7900.SplitData.node0164 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0163 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38704515693599612171477000, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0164]
theorem treeEq0163 : B0163.tree = HexagonCover.N7900.SplitData.node0163 := by
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
  · exact treeEq0164

def B0162 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38704515693599612171477000, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0163]
theorem treeEq0162 : B0162.tree = HexagonCover.N7900.SplitData.node0162 := by
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
  · exact treeEq0163

def B0161 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0162, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0161 : B0161.tree = HexagonCover.N7900.SplitData.node0161 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0162
  · rfl
  · rfl

def B0160 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0161, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0160 : B0160.tree = HexagonCover.N7900.SplitData.node0160 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0161
  · rfl

def B0159 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0160]
theorem treeEq0159 : B0159.tree = HexagonCover.N7900.SplitData.node0159 := by
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
  · exact treeEq0160

def B0202 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0202 : B0202.tree = HexagonCover.N7900.SplitData.node0202 := by
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

def B0201 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0202, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0201 : B0201.tree = HexagonCover.N7900.SplitData.node0201 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl
  · rfl

def B0200 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0201, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0200 : B0200.tree = HexagonCover.N7900.SplitData.node0200 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0201
  · rfl

def B0158 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0159, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0200]
theorem treeEq0158 : B0158.tree = HexagonCover.N7900.SplitData.node0158 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0159
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200

def B0111 : Block := .branch 74 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip0111_0112, B0158, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0111 : B0111.tree = HexagonCover.N7900.SplitData.node0111 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0158
  · rfl
  · rfl
  · rfl

theorem accepted0111 : B0111.accepted = true := by decide +kernel
theorem checked0111 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0111 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0111]
  exact B0111.sound accepted0111
#print axioms checked0111

end HexagonCover.N7900.SplitAlignedTree.Run0002
