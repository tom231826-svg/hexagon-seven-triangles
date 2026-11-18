import HexagonCover.N7900.SplitAlignedTree.Run0010
import HexagonCover.N7900.SplitAlignedTree.Run0017
import HexagonCover.N7900.SplitAlignedTree.Run0022
import HexagonCover.N7900.SplitAlignedTree.Run0027
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0028
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip1721_1734 : Block := .tip HexagonCover.N7900.SplitData.node1734 ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0027.checked1734
def B1731 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq1731 : B1731.tree = HexagonCover.N7900.SplitData.node1731 := by
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

def B1730 : Block := .branch 169 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1731, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1730 : B1730.tree = HexagonCover.N7900.SplitData.node1730 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1731
  · rfl
  · rfl

def B1729 : Block := .branch 166 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 201).pointIds 201), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B1730, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1729 : B1729.tree = HexagonCover.N7900.SplitData.node1729 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1730
  · rfl

def B1728 : Block := .branch 88 ![10141204801826411672725929066881, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1729]
theorem treeEq1728 : B1728.tree = HexagonCover.N7900.SplitData.node1728 := by
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
  · exact treeEq1729

def B1727 : Block := .branch 78 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 194).pointIds 194), B1728, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1727 : B1727.tree = HexagonCover.N7900.SplitData.node1727 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1728
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1726 : Block := .branch 133 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B1727]
theorem treeEq1726 : B1726.tree = HexagonCover.N7900.SplitData.node1726 := by
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
  · exact treeEq1727

def B1725 : Block := .branch 138 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1726, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq1725 : B1725.tree = HexagonCover.N7900.SplitData.node1725 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1726
  · rfl
  · rfl

def B1724 : Block := .branch 144 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1725, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq1724 : B1724.tree = HexagonCover.N7900.SplitData.node1724 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1725
  · rfl

def B1723 : Block := .branch 124 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1724]
theorem treeEq1723 : B1723.tree = HexagonCover.N7900.SplitData.node1723 := by
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
  · exact treeEq1724

def B2175 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 512).pointIds 512)]
theorem treeEq2175 : B2175.tree = HexagonCover.N7900.SplitData.node2175 := by
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

def B2174 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B2175, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq2174 : B2174.tree = HexagonCover.N7900.SplitData.node2174 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2175
  · rfl
  · rfl

def B2173 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B2174, (.leaf 6 (Common.fact 509).pointIds 509)]
theorem treeEq2173 : B2173.tree = HexagonCover.N7900.SplitData.node2173 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2174
  · rfl

def B1733 : Block := .branch 67 ![10141204801825835211973625643393, 720575940379280898, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), Tip1721_1734, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B2173]
theorem treeEq1733 : B1733.tree = HexagonCover.N7900.SplitData.node1733 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2173

def B2178 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq2178 : B2178.tree = HexagonCover.N7900.SplitData.node2178 := by
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

def B2177 : Block := .branch 168 ![385, 1461501637330902918203684832716859480408235968002, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B2178, (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq2177 : B2177.tree = HexagonCover.N7900.SplitData.node2177 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq2178
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2176 : Block := .branch 160 ![385, 576460752303425026, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 334).pointIds 334), B2177, (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2176 : B2176.tree = HexagonCover.N7900.SplitData.node2176 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2177
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1732 : Block := .branch 65 ![10141204801825835211973625643393, 1008806316530992642, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 225).pointIds 225), (.leaf 1 (Common.fact 703).pointIds 703), B1733, (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2176]
theorem treeEq1732 : B1732.tree = HexagonCover.N7900.SplitData.node1732 := by
  change Tree.branch (65 : Fin 170) _ = Tree.branch (65 : Fin 170) _
  apply congrArg (Tree.branch (65 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1733
  · rfl
  · rfl
  · rfl
  · exact treeEq2176

def B1722 : Block := .branch 59 ![10141204801825835211973625643393, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1723, B1732, (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq1722 : B1722.tree = HexagonCover.N7900.SplitData.node1722 := by
  change Tree.branch (59 : Fin 170) _ = Tree.branch (59 : Fin 170) _
  apply congrArg (Tree.branch (59 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1723
  · exact treeEq1732
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1721 : Block := .branch 64 ![10141204801825835211973625643393, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 166).pointIds 166), (.leaf 1 (Common.fact 702).pointIds 702), B1722, (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq1721 : B1721.tree = HexagonCover.N7900.SplitData.node1721 := by
  change Tree.branch (64 : Fin 170) _ = Tree.branch (64 : Fin 170) _
  apply congrArg (Tree.branch (64 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1722
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1721 : B1721.accepted = true := by decide +kernel
theorem checked1721 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1721 (maskNeeds ![10141204801825835211973625643393, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1721]
  exact B1721.sound accepted1721
#print axioms checked1721

def Tip1323_1333 : Block := .tip HexagonCover.N7900.SplitData.node1333 ![10141204801825835211973625643393, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0022.checked1333
def B1332 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq1332 : B1332.tree = HexagonCover.N7900.SplitData.node1332 := by
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

def B1331 : Block := .branch 169 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1332, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1331 : B1331.tree = HexagonCover.N7900.SplitData.node1331 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1332
  · rfl
  · rfl

def B1330 : Block := .branch 166 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 536).pointIds 536), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B1331, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1330 : B1330.tree = HexagonCover.N7900.SplitData.node1330 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1331
  · rfl

def B1329 : Block := .branch 88 ![10141204801826123442349777355137, 302231671076439407461890, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1330]
theorem treeEq1329 : B1329.tree = HexagonCover.N7900.SplitData.node1329 := by
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
  · exact treeEq1330

def B1328 : Block := .branch 78 ![10141204801826123442349777355137, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 534).pointIds 534), B1329, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1328 : B1328.tree = HexagonCover.N7900.SplitData.node1328 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1329
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1327 : Block := .branch 133 ![10141204801826123442349777355137, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B1328]
theorem treeEq1327 : B1327.tree = HexagonCover.N7900.SplitData.node1327 := by
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
  · exact treeEq1328

def B1326 : Block := .branch 138 ![10141204801826123442349777355137, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1327, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq1326 : B1326.tree = HexagonCover.N7900.SplitData.node1326 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1327
  · rfl
  · rfl

def B1325 : Block := .branch 144 ![10141204801826123442349777355137, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1326, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq1325 : B1325.tree = HexagonCover.N7900.SplitData.node1325 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1326
  · rfl

def B1324 : Block := .branch 124 ![10141204801826123442349777355137, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 141).pointIds 141), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1325]
theorem treeEq1324 : B1324.tree = HexagonCover.N7900.SplitData.node1324 := by
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
  · exact treeEq1325

def B1323 : Block := .branch 58 ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1324, Tip1323_1333, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 140).pointIds 140)]
theorem treeEq1323 : B1323.tree = HexagonCover.N7900.SplitData.node1323 := by
  change Tree.branch (58 : Fin 170) _ = Tree.branch (58 : Fin 170) _
  apply congrArg (Tree.branch (58 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1324
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1323 : B1323.accepted = true := by decide +kernel
theorem checked1323 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1323 (maskNeeds ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1323]
  exact B1323.sound accepted1323
#print axioms checked1323

def Tip1313_1721 : Block := .tip HexagonCover.N7900.SplitData.node1721 ![10141204801825835211973625643393, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked1721
def Tip1313_1323 : Block := .tip HexagonCover.N7900.SplitData.node1323 ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked1323
def B1321 : Block := .branch 58 ![93536104789177786765035829293842113257979682750849, 180143985094821378, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 536).pointIds 536), (.leaf 1 (Common.fact 689).pointIds 689), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 140).pointIds 140)]
theorem treeEq1321 : B1321.tree = HexagonCover.N7900.SplitData.node1321 := by
  change Tree.branch (58 : Fin 170) _ = Tree.branch (58 : Fin 170) _
  apply congrArg (Tree.branch (58 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1320 : Block := .branch 166 ![385, 180143985094821378, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 1461501659108974401460813886934225918747391557696] ![B1321, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1320 : B1320.tree = HexagonCover.N7900.SplitData.node1320 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1321
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1319 : Block := .branch 169 ![10141204801825835211973625643393, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1320, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1319 : B1319.tree = HexagonCover.N7900.SplitData.node1319 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1320
  · rfl

def B1318 : Block := .branch 142 ![10141204801825835211973625643393, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1319, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1318 : B1318.tree = HexagonCover.N7900.SplitData.node1318 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1319
  · rfl
  · rfl

def B1317 : Block := .branch 144 ![10141204801825835211973625643393, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1318, (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1317 : B1317.tree = HexagonCover.N7900.SplitData.node1317 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1318
  · rfl

def B1316 : Block := .branch 160 ![10141204801825835211973625643393, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), B1317]
theorem treeEq1316 : B1316.tree = HexagonCover.N7900.SplitData.node1316 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1317

def B1720 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq1720 : B1720.tree = HexagonCover.N7900.SplitData.node1720 := by
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

def B1719 : Block := .branch 169 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1720, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1719 : B1719.tree = HexagonCover.N7900.SplitData.node1719 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1720
  · rfl
  · rfl

def B1718 : Block := .branch 166 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 536).pointIds 536), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B1719, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1718 : B1718.tree = HexagonCover.N7900.SplitData.node1718 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1719
  · rfl

def B1717 : Block := .branch 88 ![10141204801826123442349777355137, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1718]
theorem treeEq1717 : B1717.tree = HexagonCover.N7900.SplitData.node1717 := by
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
  · exact treeEq1718

def B1716 : Block := .branch 78 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 534).pointIds 534), B1717, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1716 : B1716.tree = HexagonCover.N7900.SplitData.node1716 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1717
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1715 : Block := .branch 133 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B1716]
theorem treeEq1715 : B1715.tree = HexagonCover.N7900.SplitData.node1715 := by
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
  · exact treeEq1716

def B1714 : Block := .branch 138 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1715, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq1714 : B1714.tree = HexagonCover.N7900.SplitData.node1714 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1715
  · rfl
  · rfl

def B1713 : Block := .branch 144 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1714, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq1713 : B1713.tree = HexagonCover.N7900.SplitData.node1713 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1714
  · rfl

def B1712 : Block := .branch 124 ![10141204801826123442349777355137, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 141).pointIds 141), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1713]
theorem treeEq1712 : B1712.tree = HexagonCover.N7900.SplitData.node1712 := by
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
  · exact treeEq1713

def B1711 : Block := .branch 58 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1712, Tip1313_1721, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 140).pointIds 140)]
theorem treeEq1711 : B1711.tree = HexagonCover.N7900.SplitData.node1711 := by
  change Tree.branch (58 : Fin 170) _ = Tree.branch (58 : Fin 170) _
  apply congrArg (Tree.branch (58 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1322 : Block := .branch 56 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 131).pointIds 131), Tip1313_1323, B1711, (.leaf 3 (Common.fact 132).pointIds 132), (.leaf 4 (Common.fact 133).pointIds 133), (.leaf 5 (Common.fact 134).pointIds 134), (.leaf 6 (Common.fact 135).pointIds 135)]
theorem treeEq1322 : B1322.tree = HexagonCover.N7900.SplitData.node1322 := by
  change Tree.branch (56 : Fin 170) _ = Tree.branch (56 : Fin 170) _
  apply congrArg (Tree.branch (56 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1711
  · rfl
  · rfl
  · rfl
  · rfl

def B1315 : Block := .branch 55 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 83).pointIds 83), B1316, B1322, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 87).pointIds 87)]
theorem treeEq1315 : B1315.tree = HexagonCover.N7900.SplitData.node1315 := by
  change Tree.branch (55 : Fin 170) _ = Tree.branch (55 : Fin 170) _
  apply congrArg (Tree.branch (55 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1316
  · exact treeEq1322
  · rfl
  · rfl
  · rfl
  · rfl

def B1314 : Block := .branch 150 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B1315, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 422).pointIds 422)]
theorem treeEq1314 : B1314.tree = HexagonCover.N7900.SplitData.node1314 := by
  change Tree.branch (150 : Fin 170) _ = Tree.branch (150 : Fin 170) _
  apply congrArg (Tree.branch (150 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1315
  · rfl
  · rfl

def B1313 : Block := .branch 152 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 98).pointIds 98), B1314, (.leaf 6 (Common.fact 421).pointIds 421)]
theorem treeEq1313 : B1313.tree = HexagonCover.N7900.SplitData.node1313 := by
  change Tree.branch (152 : Fin 170) _ = Tree.branch (152 : Fin 170) _
  apply congrArg (Tree.branch (152 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1314
  · rfl

theorem accepted1313 : B1313.accepted = true := by decide +kernel
theorem checked1313 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1313 (maskNeeds ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1313]
  exact B1313.sound accepted1313
#print axioms checked1313

def Tip0013_0032 : Block := .tip HexagonCover.N7900.SplitData.node0032 ![10141204801825835211973625643393, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.N7900.SplitAlignedTree.Run0010.checked0032
def Tip0013_0858 : Block := .tip HexagonCover.N7900.SplitData.node0858 ![10141204801825835211973625643393, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.N7900.SplitAlignedTree.Run0017.checked0858
def Tip0013_1313 : Block := .tip HexagonCover.N7900.SplitData.node1313 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] checked1313
def B0021 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21778071483256974311860606179146773037120] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), (.leaf 5 (Common.fact 129).pointIds 129), (.leaf 6 (Common.fact 130).pointIds 130)]
theorem treeEq0021 : B0021.tree = HexagonCover.N7900.SplitData.node0021 := by
  change Tree.branch (129 : Fin 170) _ = Tree.branch (129 : Fin 170) _
  apply congrArg (Tree.branch (129 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0020 : Block := .branch 143 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311860606179146773037120] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0021, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 123).pointIds 123)]
theorem treeEq0020 : B0020.tree = HexagonCover.N7900.SplitData.node0020 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl

def B0019 : Block := .branch 144 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311860606179146773037120] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B0020, (.leaf 6 (Common.fact 117).pointIds 117)]
theorem treeEq0019 : B0019.tree = HexagonCover.N7900.SplitData.node0019 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl

def B0018 : Block := .branch 67 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B0019]
theorem treeEq0018 : B0018.tree = HexagonCover.N7900.SplitData.node0018 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019

def B0017 : Block := .branch 150 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0018, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 105).pointIds 105)]
theorem treeEq0017 : B0017.tree = HexagonCover.N7900.SplitData.node0017 := by
  change Tree.branch (150 : Fin 170) _ = Tree.branch (150 : Fin 170) _
  apply congrArg (Tree.branch (150 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018
  · rfl
  · rfl

def B0016 : Block := .branch 152 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 98).pointIds 98), B0017, (.leaf 6 (Common.fact 99).pointIds 99)]
theorem treeEq0016 : B0016.tree = HexagonCover.N7900.SplitData.node0016 := by
  change Tree.branch (152 : Fin 170) _ = Tree.branch (152 : Fin 170) _
  apply congrArg (Tree.branch (152 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0017
  · rfl

def B0015 : Block := .branch 88 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0016]
theorem treeEq0015 : B0015.tree = HexagonCover.N7900.SplitData.node0015 := by
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
  · exact treeEq0016

def B0031 : Block := .branch 79 ![288230376151712129, 216172782113785346, 6148, 24584, 98320, 393248, 27243857001924548381093486858429873520704] ![(.leaf 0 (Common.fact 178).pointIds 178), (.leaf 1 (Common.fact 179).pointIds 179), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), (.leaf 6 (Common.fact 184).pointIds 184)]
theorem treeEq0031 : B0031.tree = HexagonCover.N7900.SplitData.node0031 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0030 : Block := .branch 132 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0031]
theorem treeEq0030 : B0030.tree = HexagonCover.N7900.SplitData.node0030 := by
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
  · exact treeEq0031

def B0029 : Block := .branch 64 ![288230376151712129, 147790125371790198274, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 166).pointIds 166), (.leaf 1 (Common.fact 167).pointIds 167), B0030, (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq0029 : B0029.tree = HexagonCover.N7900.SplitData.node0029 := by
  change Tree.branch (64 : Fin 170) _ = Tree.branch (64 : Fin 170) _
  apply congrArg (Tree.branch (64 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0030
  · rfl
  · rfl
  · rfl
  · rfl

def B0028 : Block := .branch 67 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 32688374872659563796507480577338164904000] ![(.leaf 0 (Common.fact 106).pointIds 106), B0029, (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), (.leaf 6 (Common.fact 165).pointIds 165)]
theorem treeEq0028 : B0028.tree = HexagonCover.N7900.SplitData.node0028 := by
  change Tree.branch (67 : Fin 170) _ = Tree.branch (67 : Fin 170) _
  apply congrArg (Tree.branch (67 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0029
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0027 : Block := .branch 133 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 163).pointIds 163), (.leaf 5 (Common.fact 164).pointIds 164), B0028]
theorem treeEq0027 : B0027.tree = HexagonCover.N7900.SplitData.node0027 := by
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
  · exact treeEq0028

def B0026 : Block := .branch 138 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B0027, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 158).pointIds 158)]
theorem treeEq0026 : B0026.tree = HexagonCover.N7900.SplitData.node0026 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0027
  · rfl
  · rfl

def B0025 : Block := .branch 147 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 147).pointIds 147), (.leaf 1 (Common.fact 148).pointIds 148), (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), B0026, (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 152).pointIds 152)]
theorem treeEq0025 : B0025.tree = HexagonCover.N7900.SplitData.node0025 := by
  change Tree.branch (147 : Fin 170) _ = Tree.branch (147 : Fin 170) _
  apply congrArg (Tree.branch (147 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0026
  · rfl
  · rfl

def B0024 : Block := .branch 124 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 141).pointIds 141), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B0025]
theorem treeEq0024 : B0024.tree = HexagonCover.N7900.SplitData.node0024 := by
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
  · exact treeEq0025

def B0023 : Block := .branch 58 ![10141204801825835211973625643393, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![B0024, Tip0013_0032, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 140).pointIds 140)]
theorem treeEq0023 : B0023.tree = HexagonCover.N7900.SplitData.node0023 := by
  change Tree.branch (58 : Fin 170) _ = Tree.branch (58 : Fin 170) _
  apply congrArg (Tree.branch (58 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0024
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0022 : Block := .branch 56 ![10141204801825835211973625643393, 144255925564212738, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 131).pointIds 131), B0023, Tip0013_0858, (.leaf 3 (Common.fact 132).pointIds 132), (.leaf 4 (Common.fact 133).pointIds 133), (.leaf 5 (Common.fact 134).pointIds 134), (.leaf 6 (Common.fact 135).pointIds 135)]
theorem treeEq0022 : B0022.tree = HexagonCover.N7900.SplitData.node0022 := by
  change Tree.branch (56 : Fin 170) _ = Tree.branch (56 : Fin 170) _
  apply congrArg (Tree.branch (56 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0023
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 55 ![10141204801825835211973625643393, 144255925564212738, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 83).pointIds 83), B0015, B0022, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 87).pointIds 87)]
theorem treeEq0014 : B0014.tree = HexagonCover.N7900.SplitData.node0014 := by
  change Tree.branch (55 : Fin 170) _ = Tree.branch (55 : Fin 170) _
  apply congrArg (Tree.branch (55 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0015
  · exact treeEq0022
  · rfl
  · rfl
  · rfl
  · rfl

def B1312 : Block := .branch 87 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 231).pointIds 231), (.leaf 1 (Common.fact 232).pointIds 232), (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 234).pointIds 234), (.leaf 4 (Common.fact 235).pointIds 235), (.leaf 5 (Common.fact 236).pointIds 236), Tip0013_1313]
theorem treeEq1312 : B1312.tree = HexagonCover.N7900.SplitData.node1312 := by
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
  · rfl

def B0013 : Block := .branch 47 ![10141204801825835211973625643393, 144115188075857410, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 78).pointIds 78), B0014, B1312, (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 6 (Common.fact 82).pointIds 82)]
theorem treeEq0013 : B0013.tree = HexagonCover.N7900.SplitData.node0013 := by
  change Tree.branch (47 : Fin 170) _ = Tree.branch (47 : Fin 170) _
  apply congrArg (Tree.branch (47 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0014
  · exact treeEq1312
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0013 : B0013.accepted = true := by decide +kernel
theorem checked0013 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0013 (maskNeeds ![10141204801825835211973625643393, 144115188075857410, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0013]
  exact B0013.sound accepted0013
#print axioms checked0013

end HexagonCover.N7900.SplitAlignedTree.Run0028
