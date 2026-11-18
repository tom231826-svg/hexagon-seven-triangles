import HexagonCover.N7900.SplitAlignedTree.Run0021
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0022
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip1333_1345 : Block := .tip HexagonCover.N7900.SplitData.node1345 ![10141204801825835211973625643393, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.N7900.SplitAlignedTree.Run0021.checked1345
def B1343 : Block := .branch 141 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), (.leaf 4 (Common.fact 459).pointIds 459), (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 540).pointIds 540)]
theorem treeEq1343 : B1343.tree = HexagonCover.N7900.SplitData.node1343 := by
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

def B1342 : Block := .branch 169 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1343, (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1342 : B1342.tree = HexagonCover.N7900.SplitData.node1342 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1343
  · rfl
  · rfl

def B1341 : Block := .branch 166 ![10141204801826411672725929066881, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 201).pointIds 201), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B1342, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1341 : B1341.tree = HexagonCover.N7900.SplitData.node1341 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1342
  · rfl

def B1340 : Block := .branch 88 ![10141204801826411672725929066881, 302231671076439407461890, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1341]
theorem treeEq1340 : B1340.tree = HexagonCover.N7900.SplitData.node1340 := by
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
  · exact treeEq1341

def B1339 : Block := .branch 78 ![10141204801826411672725929066881, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 194).pointIds 194), B1340, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1339 : B1339.tree = HexagonCover.N7900.SplitData.node1339 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1340
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1338 : Block := .branch 133 ![10141204801826411672725929066881, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B1339]
theorem treeEq1338 : B1338.tree = HexagonCover.N7900.SplitData.node1338 := by
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
  · exact treeEq1339

def B1337 : Block := .branch 138 ![10141204801826411672725929066881, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1338, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq1337 : B1337.tree = HexagonCover.N7900.SplitData.node1337 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1338
  · rfl
  · rfl

def B1336 : Block := .branch 144 ![10141204801826411672725929066881, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1337, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq1336 : B1336.tree = HexagonCover.N7900.SplitData.node1336 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1337
  · rfl

def B1335 : Block := .branch 124 ![10141204801826411672725929066881, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1336]
theorem treeEq1335 : B1335.tree = HexagonCover.N7900.SplitData.node1335 := by
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
  · exact treeEq1336

def B1710 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq1710 : B1710.tree = HexagonCover.N7900.SplitData.node1710 := by
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

def B1709 : Block := .branch 168 ![385, 1461501637330902918203684832716859480408235968002, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B1710, (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1709 : B1709.tree = HexagonCover.N7900.SplitData.node1709 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1710
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1708 : Block := .branch 160 ![385, 576460752303425026, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 334).pointIds 334), B1709, (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1708 : B1708.tree = HexagonCover.N7900.SplitData.node1708 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1709
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1344 : Block := .branch 65 ![10141204801825835211973625643393, 1080863910568920578, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 225).pointIds 225), (.leaf 1 (Common.fact 420).pointIds 420), Tip1333_1345, (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1708]
theorem treeEq1344 : B1344.tree = HexagonCover.N7900.SplitData.node1344 := by
  change Tree.branch (65 : Fin 170) _ = Tree.branch (65 : Fin 170) _
  apply congrArg (Tree.branch (65 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1708

def B1334 : Block := .branch 59 ![10141204801825835211973625643393, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1335, B1344, (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq1334 : B1334.tree = HexagonCover.N7900.SplitData.node1334 := by
  change Tree.branch (59 : Fin 170) _ = Tree.branch (59 : Fin 170) _
  apply congrArg (Tree.branch (59 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1335
  · exact treeEq1344
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1333 : Block := .branch 64 ![10141204801825835211973625643393, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 166).pointIds 166), (.leaf 1 (Common.fact 185).pointIds 185), B1334, (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq1333 : B1333.tree = HexagonCover.N7900.SplitData.node1333 := by
  change Tree.branch (64 : Fin 170) _ = Tree.branch (64 : Fin 170) _
  apply congrArg (Tree.branch (64 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1334
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1333 : B1333.accepted = true := by decide +kernel
theorem checked1333 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1333 (maskNeeds ![10141204801825835211973625643393, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1333]
  exact B1333.sound accepted1333
#print axioms checked1333

def B1785 : Block := .branch 160 ![385, 374144419156711147060143317477599907935576024679938, 9223512774343137284, 24584, 98320, 393248, 16747336970383760095891472927533424719691840] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1785 : B1785.tree = HexagonCover.N7900.SplitData.node1785 := by
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
  · rfl

def B1784 : Block := .branch 168 ![42535295867593188011492586478769275265, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 16747336970383760095891472927533424719691840] ![(.leaf 0 (Common.fact 731).pointIds 731), B1785, (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 732).pointIds 732)]
theorem treeEq1784 : B1784.tree = HexagonCover.N7900.SplitData.node1784 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1785
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1783 : Block := .branch 142 ![42535295867593188011492586478769275265, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 184114956442457227707780451619480161774592950288, 5708990770823839524233143877797980545531379744, 11172150670751104310507543359371334343196736] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 496).pointIds 496), B1784]
theorem treeEq1783 : B1783.tree = HexagonCover.N7900.SplitData.node1783 := by
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
  · exact treeEq1784

def B1782 : Block := .branch 130 ![42535295867593188011492586478769275265, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 184114955081327760024026597765981732047520104464, 5708990770823839524233143877797980545531379744, 11172150670751104310507543359371334343196736] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 725).pointIds 725), (.leaf 2 (Common.fact 726).pointIds 726), (.leaf 3 (Common.fact 727).pointIds 727), B1783, (.leaf 5 (Common.fact 728).pointIds 728), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq1782 : B1782.tree = HexagonCover.N7900.SplitData.node1782 := by
  change Tree.branch (130 : Fin 170) _ = Tree.branch (130 : Fin 170) _
  apply congrArg (Tree.branch (130 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1783
  · rfl
  · rfl

def B1781 : Block := .branch 78 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114955081327760024026597765981732047520104464, 5708990770823839524233143877797980545531379744, 11172150670751104310507543359371334343196736] ![(.leaf 0 (Common.fact 722).pointIds 722), B1782, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq1781 : B1781.tree = HexagonCover.N7900.SplitData.node1781 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1782
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1780 : Block := .branch 143 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114955081327760024026597765981732047520104464, 5708990770823839524233143877797980545531379744, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 122).pointIds 122), B1781]
theorem treeEq1780 : B1780.tree = HexagonCover.N7900.SplitData.node1780 := by
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
  · exact treeEq1781

def B1779 : Block := .branch 131 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 581).pointIds 581), (.leaf 1 (Common.fact 582).pointIds 582), (.leaf 2 (Common.fact 583).pointIds 583), (.leaf 3 (Common.fact 584).pointIds 584), B1780, (.leaf 5 (Common.fact 585).pointIds 585), (.leaf 6 (Common.fact 721).pointIds 721)]
theorem treeEq1779 : B1779.tree = HexagonCover.N7900.SplitData.node1779 := by
  change Tree.branch (131 : Fin 170) _ = Tree.branch (131 : Fin 170) _
  apply congrArg (Tree.branch (131 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1780
  · rfl
  · rfl

def B1778 : Block := .branch 135 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 575).pointIds 575), (.leaf 1 (Common.fact 576).pointIds 576), (.leaf 2 (Common.fact 577).pointIds 577), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 579).pointIds 579), B1779, (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq1778 : B1778.tree = HexagonCover.N7900.SplitData.node1778 := by
  change Tree.branch (135 : Fin 170) _ = Tree.branch (135 : Fin 170) _
  apply congrArg (Tree.branch (135 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1779
  · rfl

def B1777 : Block := .branch 101 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 719).pointIds 719), (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), B1778]
theorem treeEq1777 : B1777.tree = HexagonCover.N7900.SplitData.node1777 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1778

def B1776 : Block := .branch 112 ![93536104789220322060903422481853605844458452025729, 1538, 9223512774343137284, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 713).pointIds 713), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1777]
theorem treeEq1776 : B1776.tree = HexagonCover.N7900.SplitData.node1776 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1777

def B1775 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 1538, 9223512774343137284, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![B1776, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1775 : B1775.tree = HexagonCover.N7900.SplitData.node1775 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1776
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1774 : Block := .branch 157 ![93536104789177786765038305173920684018529480999297, 1538, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1775, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1774 : B1774.tree = HexagonCover.N7900.SplitData.node1774 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1775
  · rfl
  · rfl

def B1773 : Block := .branch 166 ![2475880078570760549798248833, 1538, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 21778071483257438539227764244160183795776] ![B1774, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1773 : B1773.tree = HexagonCover.N7900.SplitData.node1773 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1774
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1772 : Block := .branch 169 ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 565).pointIds 565), B1773, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1772 : B1772.tree = HexagonCover.N7900.SplitData.node1772 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1773
  · rfl

def B1771 : Block := .branch 141 ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B1772, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 564).pointIds 564)]
theorem treeEq1771 : B1771.tree = HexagonCover.N7900.SplitData.node1771 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1772
  · rfl
  · rfl

def B1770 : Block := .branch 144 ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1771, (.leaf 6 (Common.fact 563).pointIds 563)]
theorem treeEq1770 : B1770.tree = HexagonCover.N7900.SplitData.node1770 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1771
  · rfl

theorem accepted1770 : B1770.accepted = true := by decide +kernel
theorem checked1770 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1770 (maskNeeds ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152]) := by
  rw [← treeEq1770]
  exact B1770.sound accepted1770
#print axioms checked1770

def B1796 : Block := .branch 124 ![10384593717674118166868307245793665, 1538, 6148, 24584, 98320, 393248, 11692024270797894094198023816860296433899633377344] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq1796 : B1796.tree = HexagonCover.N7900.SplitData.node1796 := by
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

def B1795 : Block := .branch 143 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886453049001160109718880387136] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 122).pointIds 122), B1796]
theorem treeEq1795 : B1795.tree = HexagonCover.N7900.SplitData.node1795 := by
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
  · exact treeEq1796

def B1794 : Block := .branch 101 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886453049001160109718880387136] ![B1795, (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq1794 : B1794.tree = HexagonCover.N7900.SplitData.node1794 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1795
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1793 : Block := .branch 163 ![10384593717674118166868307245793665, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 247).pointIds 247), B1794]
theorem treeEq1793 : B1793.tree = HexagonCover.N7900.SplitData.node1793 := by
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
  · exact treeEq1794

def B1792 : Block := .branch 169 ![10394734922475944002080280871436673, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071483257129129775806625005782433856] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1793, (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1792 : B1792.tree = HexagonCover.N7900.SplitData.node1792 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1793
  · rfl
  · rfl

def B1791 : Block := .branch 125 ![10394734922475944002080280871436673, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), B1792, (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1791 : B1791.tree = HexagonCover.N7900.SplitData.node1791 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1792
  · rfl

def B1798 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483256974991733805759786007396416] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq1798 : B1798.tree = HexagonCover.N7900.SplitData.node1798 := by
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

def B1797 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483256974991733805759786007396416] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1798, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1797 : B1797.tree = HexagonCover.N7900.SplitData.node1797 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1798
  · rfl
  · rfl

def B1790 : Block := .branch 79 ![10394734921871481092272966284083585, 618970019786805325525419522, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![B1791, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 180).pointIds 180), (.leaf 3 (Common.fact 181).pointIds 181), (.leaf 4 (Common.fact 182).pointIds 182), (.leaf 5 (Common.fact 183).pointIds 183), B1797]
theorem treeEq1790 : B1790.tree = HexagonCover.N7900.SplitData.node1790 := by
  change Tree.branch (79 : Fin 170) _ = Tree.branch (79 : Fin 170) _
  apply congrArg (Tree.branch (79 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1791
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1797

def B1806 : Block := .branch 101 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 21799339131190152011256999555573355118656] ![(.leaf 0 (Common.fact 611).pointIds 611), (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq1806 : B1806.tree = HexagonCover.N7900.SplitData.node1806 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1805 : Block := .branch 124 ![42545680458834378178474697280335118721, 1538, 6148, 24584, 98320, 393248, 21778071483257593357290538642608869605440] ![(.leaf 0 (Common.fact 610).pointIds 610), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1806]
theorem treeEq1805 : B1805.tree = HexagonCover.N7900.SplitData.node1805 := by
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
  · exact treeEq1806

def B1804 : Block := .branch 125 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![B1805, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1804 : B1804.tree = HexagonCover.N7900.SplitData.node1804 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1805
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1803 : Block := .branch 157 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1804, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1803 : B1803.tree = HexagonCover.N7900.SplitData.node1803 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1804
  · rfl
  · rfl

def B1802 : Block := .branch 166 ![10384593717070245552871351364092289, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483258057584805270660211956777024] ![B1803, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1802 : B1802.tree = HexagonCover.N7900.SplitData.node1802 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1803
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1801 : Block := .branch 169 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1802, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1801 : B1801.tree = HexagonCover.N7900.SplitData.node1801 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1802
  · rfl

def B1800 : Block := .branch 143 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1801, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 609).pointIds 609)]
theorem treeEq1800 : B1800.tree = HexagonCover.N7900.SplitData.node1800 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1801
  · rfl
  · rfl

def B1799 : Block := .branch 144 ![10394734921872071388083324989735297, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1800, (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq1799 : B1799.tree = HexagonCover.N7900.SplitData.node1799 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1800
  · rfl

def B1789 : Block := .branch 89 ![10394737397752149958843874787983745, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 736).pointIds 736), B1790, (.leaf 2 (Common.fact 521).pointIds 521), (.leaf 3 (Common.fact 522).pointIds 522), (.leaf 4 (Common.fact 523).pointIds 523), (.leaf 5 (Common.fact 524).pointIds 524), B1799]
theorem treeEq1789 : B1789.tree = HexagonCover.N7900.SplitData.node1789 := by
  change Tree.branch (89 : Fin 170) _ = Tree.branch (89 : Fin 170) _
  apply congrArg (Tree.branch (89 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1790
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1799

theorem accepted1789 : B1789.accepted = true := by decide +kernel
theorem checked1789 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1789 (maskNeeds ![10394737397752149958843874787983745, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1789]
  exact B1789.sound accepted1789
#print axioms checked1789

def Tip1786_1789 : Block := .tip HexagonCover.N7900.SplitData.node1789 ![10394737397752149958843874787983745, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] checked1789
def B1809 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq1809 : B1809.tree = HexagonCover.N7900.SplitData.node1809 := by
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

def B1808 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1809, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 614).pointIds 614)]
theorem treeEq1808 : B1808.tree = HexagonCover.N7900.SplitData.node1808 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1809
  · rfl
  · rfl

def B1807 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483256974689502350856128713719872] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1808, (.leaf 6 (Common.fact 613).pointIds 613)]
theorem treeEq1807 : B1807.tree = HexagonCover.N7900.SplitData.node1807 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1808
  · rfl

def B1788 : Block := .branch 78 ![10394737397752149958843874787983745, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 735).pointIds 735), Tip1786_1789, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1807]
theorem treeEq1788 : B1788.tree = HexagonCover.N7900.SplitData.node1788 := by
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
  · exact treeEq1807

def B1822 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), (.leaf 4 (Common.fact 672).pointIds 672), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1822 : B1822.tree = HexagonCover.N7900.SplitData.node1822 := by
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

def B1821 : Block := .branch 101 ![42545680461310257666749647471427715457, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 746).pointIds 746), (.leaf 1 (Common.fact 570).pointIds 570), (.leaf 2 (Common.fact 571).pointIds 571), (.leaf 3 (Common.fact 572).pointIds 572), (.leaf 4 (Common.fact 573).pointIds 573), (.leaf 5 (Common.fact 574).pointIds 574), B1822]
theorem treeEq1821 : B1821.tree = HexagonCover.N7900.SplitData.node1821 := by
  change Tree.branch (101 : Fin 170) _ = Tree.branch (101 : Fin 170) _
  apply congrArg (Tree.branch (101 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1822

def B1820 : Block := .branch 118 ![42545680461310257666749647471427715457, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778076675553832922098524482967749263424] ![(.leaf 0 (Common.fact 266).pointIds 266), (.leaf 1 (Common.fact 267).pointIds 267), (.leaf 2 (Common.fact 268).pointIds 268), B1821, (.leaf 4 (Common.fact 744).pointIds 744), (.leaf 5 (Common.fact 270).pointIds 270), (.leaf 6 (Common.fact 745).pointIds 745)]
theorem treeEq1820 : B1820.tree = HexagonCover.N7900.SplitData.node1820 := by
  change Tree.branch (118 : Fin 170) _ = Tree.branch (118 : Fin 170) _
  apply congrArg (Tree.branch (118 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1821
  · rfl
  · rfl
  · rfl

def B1819 : Block := .branch 139 ![42545680461310257666749647471427715457, 1538, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 393248, 21778076675553832922098524482967749263424] ![(.leaf 0 (Common.fact 641).pointIds 641), (.leaf 1 (Common.fact 642).pointIds 642), (.leaf 2 (Common.fact 643).pointIds 643), (.leaf 3 (Common.fact 644).pointIds 644), B1820, (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 743).pointIds 743)]
theorem treeEq1819 : B1819.tree = HexagonCover.N7900.SplitData.node1819 := by
  change Tree.branch (139 : Fin 170) _ = Tree.branch (139 : Fin 170) _
  apply congrArg (Tree.branch (139 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1820
  · rfl
  · rfl

def B1818 : Block := .branch 112 ![42545680461310257666749647471427715457, 1538, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1819]
theorem treeEq1818 : B1818.tree = HexagonCover.N7900.SplitData.node1818 := by
  change Tree.branch (112 : Fin 170) _ = Tree.branch (112 : Fin 170) _
  apply congrArg (Tree.branch (112 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1819

def B1817 : Block := .branch 159 ![42545680461310257666749647471427715457, 737869762948382066178, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 740).pointIds 740), (.leaf 1 (Common.fact 741).pointIds 741), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B1818]
theorem treeEq1817 : B1817.tree = HexagonCover.N7900.SplitData.node1817 := by
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
  · exact treeEq1818

def B1816 : Block := .branch 125 ![10384596192949733827821542456689025, 737869762948382066178, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![B1817, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1816 : B1816.tree = HexagonCover.N7900.SplitData.node1816 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1817
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1815 : Block := .branch 157 ![10384596192949733827821542456689025, 737869762948382066178, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1816, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1815 : B1815.tree = HexagonCover.N7900.SplitData.node1815 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1816
  · rfl
  · rfl

def B1814 : Block := .branch 166 ![10384596192949733827821542456689025, 737869762948382066178, 6148, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![B1815, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1814 : B1814.tree = HexagonCover.N7900.SplitData.node1814 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1815
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1813 : Block := .branch 169 ![10394737397751559663033516082332033, 738013878136457922050, 9223512774343137284, 79266848140492005727134572552, 11150372599265311570767859136324180753088528, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1814, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1813 : B1813.tree = HexagonCover.N7900.SplitData.node1813 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1814
  · rfl

def B1812 : Block := .branch 143 ![10394737397751559663033516082332033, 738013878136457922050, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1813, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq1812 : B1812.tree = HexagonCover.N7900.SplitData.node1812 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1813
  · rfl
  · rfl

def B1811 : Block := .branch 144 ![10394737397751559663033516082332033, 738013878136457922050, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 1461501659108974401461123447501910989730439757888] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1812, (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq1811 : B1811.tree = HexagonCover.N7900.SplitData.node1811 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1812
  · rfl

def B1810 : Block := .branch 160 ![10394737397751559663033516082332033, 738013878136457922050, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 737).pointIds 737), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), B1811]
theorem treeEq1810 : B1810.tree = HexagonCover.N7900.SplitData.node1810 := by
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
  · exact treeEq1811

def B1787 : Block := .branch 69 ![10394737397751559663033516082332033, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912] ![B1788, B1810, (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 426).pointIds 426), (.leaf 5 (Common.fact 427).pointIds 427), (.leaf 6 (Common.fact 734).pointIds 734)]
theorem treeEq1787 : B1787.tree = HexagonCover.N7900.SplitData.node1787 := by
  change Tree.branch (69 : Fin 170) _ = Tree.branch (69 : Fin 170) _
  apply congrArg (Tree.branch (69 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1788
  · exact treeEq1810
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1786 : Block := .branch 113 ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912] ![B1787, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 598).pointIds 598)]
theorem treeEq1786 : B1786.tree = HexagonCover.N7900.SplitData.node1786 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1787
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1786 : B1786.accepted = true := by decide +kernel
theorem checked1786 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1786 (maskNeeds ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1786]
  exact B1786.sound accepted1786
#print axioms checked1786

def Tip1761_1770 : Block := .tip HexagonCover.N7900.SplitData.node1770 ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071484525089139455993645656887001152] checked1770
def Tip1761_1786 : Block := .tip HexagonCover.N7900.SplitData.node1786 ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 98320, 393248, 21778071483257438614785627970074507214912] checked1786
def B1769 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 11692024270797894094198487968817164725588397129792] ![(.leaf 0 (Common.fact 561).pointIds 561), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 562).pointIds 562)]
theorem treeEq1769 : B1769.tree = HexagonCover.N7900.SplitData.node1769 := by
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

def B1768 : Block := .branch 143 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886917200958028401407644139584] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 517).pointIds 517), (.leaf 5 (Common.fact 122).pointIds 122), B1769]
theorem treeEq1768 : B1768.tree = HexagonCover.N7900.SplitData.node1768 := by
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
  · exact treeEq1769

def B1767 : Block := .branch 113 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 11692013120425294828886917200958028401407644139584] ![B1768, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 560).pointIds 560)]
theorem treeEq1767 : B1767.tree = HexagonCover.N7900.SplitData.node1767 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1766 : Block := .branch 163 ![1267650600228229401496703205761, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 559).pointIds 559), (.leaf 5 (Common.fact 247).pointIds 247), B1767]
theorem treeEq1766 : B1766.tree = HexagonCover.N7900.SplitData.node1766 := by
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
  · exact treeEq1767

def B1765 : Block := .branch 169 ![11408855402054064613470328848769, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1766, (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1765 : B1765.tree = HexagonCover.N7900.SplitData.node1765 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1766
  · rfl
  · rfl

def B1764 : Block := .branch 125 ![11408855402054064613470328848769, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 557).pointIds 557), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), B1765, (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1764 : B1764.tree = HexagonCover.N7900.SplitData.node1764 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1765
  · rfl

def B1763 : Block := .branch 100 ![10143680681904405972523423891841, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B1764, (.leaf 1 (Common.fact 552).pointIds 552), (.leaf 2 (Common.fact 553).pointIds 553), (.leaf 3 (Common.fact 554).pointIds 554), (.leaf 4 (Common.fact 555).pointIds 555), (.leaf 5 (Common.fact 556).pointIds 556), Tip1761_1770]
theorem treeEq1763 : B1763.tree = HexagonCover.N7900.SplitData.node1763 := by
  change Tree.branch (100 : Fin 170) _ = Tree.branch (100 : Fin 170) _
  apply congrArg (Tree.branch (100 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1764
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1762 : Block := .branch 76 ![10143680681904405972523423891841, 442865972957105096194, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1763, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), Tip1761_1786]
theorem treeEq1762 : B1762.tree = HexagonCover.N7900.SplitData.node1762 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1763
  · rfl
  · rfl
  · rfl
  · rfl

def B1825 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 618).pointIds 618)]
theorem treeEq1825 : B1825.tree = HexagonCover.N7900.SplitData.node1825 := by
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

def B1824 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1825, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 617).pointIds 617)]
theorem treeEq1824 : B1824.tree = HexagonCover.N7900.SplitData.node1824 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1825
  · rfl
  · rfl

def B1823 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054513090804270811840576] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1824, (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1823 : B1823.tree = HexagonCover.N7900.SplitData.node1823 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1824
  · rfl

def B1761 : Block := .branch 68 ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 711).pointIds 711), B1762, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B1823]
theorem treeEq1761 : B1761.tree = HexagonCover.N7900.SplitData.node1761 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1762
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1823

theorem accepted1761 : B1761.accepted = true := by decide +kernel
theorem checked1761 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1761 (maskNeeds ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1761]
  exact B1761.sound accepted1761
#print axioms checked1761

end HexagonCover.N7900.SplitAlignedTree.Run0022
