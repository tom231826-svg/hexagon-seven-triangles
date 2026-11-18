import HexagonCover.N7900.SplitAlignedTree.Run0000
import HexagonCover.N7900.SplitAlignedTree.Run0004
import HexagonCover.N7900.SplitAlignedTree.Run0005
import HexagonCover.N7900.SplitAlignedTree.Run0009
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0010
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0109_0445 : Block := .tip HexagonCover.N7900.SplitData.node0445 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0004.checked0445
def Tip0109_0387 : Block := .tip HexagonCover.N7900.SplitData.node0387 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0004.checked0387
def Tip0109_0295 : Block := .tip HexagonCover.N7900.SplitData.node0295 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0005.checked0295
def Tip0109_0110 : Block := .tip HexagonCover.N7900.SplitData.node0110 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0005.checked0110
def B0444 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0444 : B0444.tree = HexagonCover.N7900.SplitData.node0444 := by
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

def B0443 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0444, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0443 : B0443.tree = HexagonCover.N7900.SplitData.node0443 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0444
  · rfl
  · rfl

def B0442 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0443, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0442 : B0442.tree = HexagonCover.N7900.SplitData.node0442 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0443
  · rfl

def B0441 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0442]
theorem treeEq0441 : B0441.tree = HexagonCover.N7900.SplitData.node0441 := by
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
  · exact treeEq0442

def B0440 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0441]
theorem treeEq0440 : B0440.tree = HexagonCover.N7900.SplitData.node0440 := by
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
  · exact treeEq0441

def B0439 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0440, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0439 : B0439.tree = HexagonCover.N7900.SplitData.node0439 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0440
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0438 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0439, Tip0109_0445, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0438 : B0438.tree = HexagonCover.N7900.SplitData.node0438 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0439
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0437 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0438]
theorem treeEq0437 : B0437.tree = HexagonCover.N7900.SplitData.node0437 := by
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
  · exact treeEq0438

def B0436 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38690348594151003235835912, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0437]
theorem treeEq0436 : B0436.tree = HexagonCover.N7900.SplitData.node0436 := by
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
  · exact treeEq0437

def B0435 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0436, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0435 : B0435.tree = HexagonCover.N7900.SplitData.node0435 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0436
  · rfl
  · rfl

def B0434 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0435, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0434 : B0434.tree = HexagonCover.N7900.SplitData.node0434 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0435
  · rfl

def B0433 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0434]
theorem treeEq0433 : B0433.tree = HexagonCover.N7900.SplitData.node0433 := by
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
  · exact treeEq0434

def B0476 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0476 : B0476.tree = HexagonCover.N7900.SplitData.node0476 := by
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

def B0475 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0476, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0475 : B0475.tree = HexagonCover.N7900.SplitData.node0475 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0476
  · rfl
  · rfl

def B0474 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0475, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0474 : B0474.tree = HexagonCover.N7900.SplitData.node0474 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0475
  · rfl

def B0432 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0433, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0474]
theorem treeEq0432 : B0432.tree = HexagonCover.N7900.SplitData.node0432 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0433
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0474

def B0386 : Block := .branch 74 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip0109_0387, B0432, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0386 : B0386.tree = HexagonCover.N7900.SplitData.node0386 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0432
  · rfl
  · rfl
  · rfl

def B0294 : Block := .branch 73 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip0109_0295, B0386, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0294 : B0294.tree = HexagonCover.N7900.SplitData.node0294 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl
  · rfl
  · rfl

def B0109 : Block := .branch 72 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), Tip0109_0110, B0294, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0109 : B0109.tree = HexagonCover.N7900.SplitData.node0109 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0294
  · rfl
  · rfl
  · rfl

theorem accepted0109 : B0109.accepted = true := by decide +kernel
theorem checked0109 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0109 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0109]
  exact B0109.sound accepted0109
#print axioms checked0109

def Tip0108_0812 : Block := .tip HexagonCover.N7900.SplitData.node0812 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] HexagonCover.N7900.SplitAlignedTree.Run0009.checked0812
def Tip0108_0754 : Block := .tip HexagonCover.N7900.SplitData.node0754 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0009.checked0754
def Tip0108_0662 : Block := .tip HexagonCover.N7900.SplitData.node0662 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0009.checked0662
def Tip0108_0478 : Block := .tip HexagonCover.N7900.SplitData.node0478 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0009.checked0478
def Tip0108_0109 : Block := .tip HexagonCover.N7900.SplitData.node0109 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] checked0109
def B0811 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0811 : B0811.tree = HexagonCover.N7900.SplitData.node0811 := by
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

def B0810 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0811, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0810 : B0810.tree = HexagonCover.N7900.SplitData.node0810 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0811
  · rfl
  · rfl

def B0809 : Block := .branch 166 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0810, (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0809 : B0809.tree = HexagonCover.N7900.SplitData.node0809 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0810
  · rfl

def B0808 : Block := .branch 88 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0809]
theorem treeEq0808 : B0808.tree = HexagonCover.N7900.SplitData.node0808 := by
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
  · exact treeEq0809

def B0807 : Block := .branch 159 ![10141205406583892924467565822337, 374144419156711147060143317175369389780641224066562, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 444).pointIds 444), (.leaf 1 (Common.fact 445).pointIds 445), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B0808]
theorem treeEq0807 : B0807.tree = HexagonCover.N7900.SplitData.node0807 := by
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
  · exact treeEq0808

def B0806 : Block := .branch 168 ![10141205406583892924467565822337, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 438).pointIds 438), B0807, (.leaf 2 (Common.fact 439).pointIds 439), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 443).pointIds 443)]
theorem treeEq0806 : B0806.tree = HexagonCover.N7900.SplitData.node0806 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0807
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0805 : Block := .branch 68 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 348449143727040986586495598010130648629264, 393248, 38132892743394733954426384968780818677824] ![B0806, Tip0108_0812, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq0805 : B0805.tree = HexagonCover.N7900.SplitData.node0805 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0806
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0804 : Block := .branch 132 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B0805]
theorem treeEq0804 : B0804.tree = HexagonCover.N7900.SplitData.node0804 := by
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
  · exact treeEq0805

def B0803 : Block := .branch 133 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 38687987410909568413229064, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B0804]
theorem treeEq0803 : B0803.tree = HexagonCover.N7900.SplitData.node0803 := by
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
  · exact treeEq0804

def B0802 : Block := .branch 138 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0803, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq0802 : B0802.tree = HexagonCover.N7900.SplitData.node0802 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0803
  · rfl
  · rfl

def B0801 : Block := .branch 144 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0802, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0801 : B0801.tree = HexagonCover.N7900.SplitData.node0801 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0802
  · rfl

def B0800 : Block := .branch 124 ![10141205406288745019288212996481, 148510701312169477634, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 428).pointIds 428), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0801]
theorem treeEq0800 : B0800.tree = HexagonCover.N7900.SplitData.node0800 := by
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
  · exact treeEq0801

def B0843 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 500).pointIds 500), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 501).pointIds 501)]
theorem treeEq0843 : B0843.tree = HexagonCover.N7900.SplitData.node0843 := by
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

def B0842 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B0843, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0842 : B0842.tree = HexagonCover.N7900.SplitData.node0842 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl
  · rfl

def B0841 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0842, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0841 : B0841.tree = HexagonCover.N7900.SplitData.node0841 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0842
  · rfl

def B0799 : Block := .branch 79 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B0800, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B0841]
theorem treeEq0799 : B0799.tree = HexagonCover.N7900.SplitData.node0799 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0800
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0841

def B0753 : Block := .branch 74 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), Tip0108_0754, B0799, (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0753 : B0753.tree = HexagonCover.N7900.SplitData.node0753 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0799
  · rfl
  · rfl
  · rfl

def B0661 : Block := .branch 73 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), Tip0108_0662, B0753, (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0661 : B0661.tree = HexagonCover.N7900.SplitData.node0661 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0753
  · rfl
  · rfl
  · rfl

def B0477 : Block := .branch 72 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), Tip0108_0478, B0661, (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0477 : B0477.tree = HexagonCover.N7900.SplitData.node0477 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0661
  · rfl
  · rfl
  · rfl

def B0108 : Block := .branch 71 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), Tip0108_0109, B0477, (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq0108 : B0108.tree = HexagonCover.N7900.SplitData.node0108 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0477
  · rfl
  · rfl
  · rfl

theorem accepted0108 : B0108.accepted = true := by decide +kernel
theorem checked0108 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0108 (maskNeeds ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0108]
  exact B0108.sound accepted0108
#print axioms checked0108

def Tip0102_0108 : Block := .tip HexagonCover.N7900.SplitData.node0108 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] checked0108
def B0845 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0845 : B0845.tree = HexagonCover.N7900.SplitData.node0845 := by
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
  · rfl

def B0844 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B0845, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq0844 : B0844.tree = HexagonCover.N7900.SplitData.node0844 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0845
  · rfl
  · rfl

def B0107 : Block := .branch 69 ![10141204801825835211973625643393, 148654816500245333506, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![Tip0102_0108, (.leaf 1 (Common.fact 423).pointIds 423), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 426).pointIds 426), (.leaf 5 (Common.fact 427).pointIds 427), B0844]
theorem treeEq0107 : B0107.tree = HexagonCover.N7900.SplitData.node0107 := by
  change Tree.branch (69 : Fin 170) _ = Tree.branch (69 : Fin 170) _
  apply congrArg (Tree.branch (69 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0844

def B0848 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq0848 : B0848.tree = HexagonCover.N7900.SplitData.node0848 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0847 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0848, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq0847 : B0847.tree = HexagonCover.N7900.SplitData.node0847 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0848
  · rfl
  · rfl

def B0846 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0847, (.leaf 6 (Common.fact 509).pointIds 509)]
theorem treeEq0846 : B0846.tree = HexagonCover.N7900.SplitData.node0846 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0847
  · rfl

def B0106 : Block := .branch 67 ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), B0107, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B0846]
theorem treeEq0106 : B0106.tree = HexagonCover.N7900.SplitData.node0106 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0107
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0846

def B0105 : Block := .branch 150 ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0106, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 422).pointIds 422)]
theorem treeEq0105 : B0105.tree = HexagonCover.N7900.SplitData.node0105 := by
  change Tree.branch (150 : Fin 170) _ = Tree.branch (150 : Fin 170) _
  apply congrArg (Tree.branch (150 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0106
  · rfl
  · rfl

def B0104 : Block := .branch 152 ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 98).pointIds 98), B0105, (.leaf 6 (Common.fact 421).pointIds 421)]
theorem treeEq0104 : B0104.tree = HexagonCover.N7900.SplitData.node0104 := by
  change Tree.branch (152 : Fin 170) _ = Tree.branch (152 : Fin 170) _
  apply congrArg (Tree.branch (152 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0105
  · rfl

def B0103 : Block := .branch 87 ![10141204801825835211973625643393, 1080863910568920578, 55376261018147624964, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 231).pointIds 231), (.leaf 1 (Common.fact 232).pointIds 232), (.leaf 2 (Common.fact 233).pointIds 233), (.leaf 3 (Common.fact 234).pointIds 234), (.leaf 4 (Common.fact 235).pointIds 235), (.leaf 5 (Common.fact 236).pointIds 236), B0104]
theorem treeEq0103 : B0103.tree = HexagonCover.N7900.SplitData.node0103 := by
  change Tree.branch (87 : Fin 170) _ = Tree.branch (87 : Fin 170) _
  apply congrArg (Tree.branch (87 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0104

def B0857 : Block := .branch 124 ![93536104789177786765037067233881398638254581875073, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq0857 : B0857.tree = HexagonCover.N7900.SplitData.node0857 := by
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
  · rfl

def B0856 : Block := .branch 90 ![93536104789177786765035829293842113257979682750849, 618970019642690137449563650, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![B0857, (.leaf 1 (Common.fact 526).pointIds 526), (.leaf 2 (Common.fact 527).pointIds 527), (.leaf 3 (Common.fact 528).pointIds 528), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 530).pointIds 530), (.leaf 6 (Common.fact 531).pointIds 531)]
theorem treeEq0856 : B0856.tree = HexagonCover.N7900.SplitData.node0856 := by
  change Tree.branch (90 : Fin 170) _ = Tree.branch (90 : Fin 170) _
  apply congrArg (Tree.branch (90 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0857
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0855 : Block := .branch 89 ![93536104789177786765035829293842113257979682750849, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 520).pointIds 520), B0856, (.leaf 2 (Common.fact 521).pointIds 521), (.leaf 3 (Common.fact 522).pointIds 522), (.leaf 4 (Common.fact 523).pointIds 523), (.leaf 5 (Common.fact 524).pointIds 524), (.leaf 6 (Common.fact 525).pointIds 525)]
theorem treeEq0855 : B0855.tree = HexagonCover.N7900.SplitData.node0855 := by
  change Tree.branch (89 : Fin 170) _ = Tree.branch (89 : Fin 170) _
  apply congrArg (Tree.branch (89 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0856
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0854 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483256974311749925714704515727424] ![B0855, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 519).pointIds 519)]
theorem treeEq0854 : B0854.tree = HexagonCover.N7900.SplitData.node0854 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0855
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0853 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B0854, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0853 : B0853.tree = HexagonCover.N7900.SplitData.node0853 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0854
  · rfl

def B0852 : Block := .branch 143 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0853, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0852 : B0852.tree = HexagonCover.N7900.SplitData.node0852 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0853
  · rfl
  · rfl

def B0851 : Block := .branch 144 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0852, (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0851 : B0851.tree = HexagonCover.N7900.SplitData.node0851 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0852
  · rfl

def B0850 : Block := .branch 150 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0851, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 514).pointIds 514)]
theorem treeEq0850 : B0850.tree = HexagonCover.N7900.SplitData.node0850 := by
  change Tree.branch (150 : Fin 170) _ = Tree.branch (150 : Fin 170) _
  apply congrArg (Tree.branch (150 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0851
  · rfl
  · rfl

def B0849 : Block := .branch 152 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 98).pointIds 98), B0850, (.leaf 6 (Common.fact 513).pointIds 513)]
theorem treeEq0849 : B0849.tree = HexagonCover.N7900.SplitData.node0849 := by
  change Tree.branch (152 : Fin 170) _ = Tree.branch (152 : Fin 170) _
  apply congrArg (Tree.branch (152 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0850
  · rfl

def B0102 : Block := .branch 65 ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 225).pointIds 225), (.leaf 1 (Common.fact 420).pointIds 420), B0103, (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B0849]
theorem treeEq0102 : B0102.tree = HexagonCover.N7900.SplitData.node0102 := by
  change Tree.branch (65 : Fin 170) _ = Tree.branch (65 : Fin 170) _
  apply congrArg (Tree.branch (65 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl
  · exact treeEq0849

theorem accepted0102 : B0102.accepted = true := by decide +kernel
theorem checked0102 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0102 (maskNeeds ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0102]
  exact B0102.sound accepted0102
#print axioms checked0102

def Tip0032_0044 : Block := .tip HexagonCover.N7900.SplitData.node0044 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] HexagonCover.N7900.SplitAlignedTree.Run0000.checked0044
def Tip0032_0102 : Block := .tip HexagonCover.N7900.SplitData.node0102 ![10141204801825835211973625643393, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] checked0102
def B0043 : Block := .branch 78 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] ![(.leaf 0 (Common.fact 194).pointIds 194), Tip0032_0044, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 199).pointIds 199)]
theorem treeEq0043 : B0043.tree = HexagonCover.N7900.SplitData.node0043 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0042 : Block := .branch 79 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] ![B0043, (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), (.leaf 6 (Common.fact 184).pointIds 184)]
theorem treeEq0042 : B0042.tree = HexagonCover.N7900.SplitData.node0042 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0043
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0041 : Block := .branch 144 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0042, (.leaf 6 (Common.fact 193).pointIds 193)]
theorem treeEq0041 : B0041.tree = HexagonCover.N7900.SplitData.node0041 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0042
  · rfl

def B0040 : Block := .branch 152 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 98).pointIds 98), B0041, (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0040 : B0040.tree = HexagonCover.N7900.SplitData.node0040 := by
  change Tree.branch (152 : Fin 170) _ = Tree.branch (152 : Fin 170) _
  apply congrArg (Tree.branch (152 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0041
  · rfl

def B0039 : Block := .branch 132 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.N7900.SplitData.node0039 := by
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
  · exact treeEq0040

def B0038 : Block := .branch 67 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 32688374872659563796507480577338164904000] ![(.leaf 0 (Common.fact 106).pointIds 106), B0039, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), (.leaf 6 (Common.fact 165).pointIds 165)]
theorem treeEq0038 : B0038.tree = HexagonCover.N7900.SplitData.node0038 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0037 : Block := .branch 133 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 163).pointIds 163), (.leaf 5 (Common.fact 164).pointIds 164), B0038]
theorem treeEq0037 : B0037.tree = HexagonCover.N7900.SplitData.node0037 := by
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
  · exact treeEq0038

def B0036 : Block := .branch 138 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0037, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 158).pointIds 158)]
theorem treeEq0036 : B0036.tree = HexagonCover.N7900.SplitData.node0036 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037
  · rfl
  · rfl

def B0035 : Block := .branch 147 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 147).pointIds 147), (.leaf 1 (Common.fact 148).pointIds 148), (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), B0036, (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 152).pointIds 152)]
theorem treeEq0035 : B0035.tree = HexagonCover.N7900.SplitData.node0035 := by
  change Tree.branch (147 : Fin 170) _ = Tree.branch (147 : Fin 170) _
  apply congrArg (Tree.branch (147 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0036
  · rfl
  · rfl

def B0034 : Block := .branch 124 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0035]
theorem treeEq0034 : B0034.tree = HexagonCover.N7900.SplitData.node0034 := by
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
  · exact treeEq0035

def B0033 : Block := .branch 59 ![10141204801825835211973625643393, 504403158265497090, 27724229674836957188, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![B0034, Tip0032_0102, (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq0033 : B0033.tree = HexagonCover.N7900.SplitData.node0033 := by
  change Tree.branch (59 : Fin 170) _ = Tree.branch (59 : Fin 170) _
  apply congrArg (Tree.branch (59 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0034
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0032 : Block := .branch 64 ![10141204801825835211973625643393, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 166).pointIds 166), (.leaf 1 (Common.fact 185).pointIds 185), B0033, (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq0032 : B0032.tree = HexagonCover.N7900.SplitData.node0032 := by
  change Tree.branch (64 : Fin 170) _ = Tree.branch (64 : Fin 170) _
  apply congrArg (Tree.branch (64 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0033
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0032 : B0032.accepted = true := by decide +kernel
theorem checked0032 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0032 (maskNeeds ![10141204801825835211973625643393, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0032]
  exact B0032.sound accepted0032
#print axioms checked0032

end HexagonCover.N7900.SplitAlignedTree.Run0010
