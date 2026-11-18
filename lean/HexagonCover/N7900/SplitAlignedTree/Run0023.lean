import HexagonCover.N7900.SplitAlignedTree.Run0022
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0023
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B1754 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq1754 : B1754.tree = HexagonCover.N7900.SplitData.node1754 := by
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

def B1753 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B1754]
theorem treeEq1753 : B1753.tree = HexagonCover.N7900.SplitData.node1753 := by
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
  · exact treeEq1754

def B1752 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B1753, (.leaf 0 [] 0)]
theorem treeEq1752 : B1752.tree = HexagonCover.N7900.SplitData.node1752 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1753
  · rfl

def B1751 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B1752, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq1751 : B1751.tree = HexagonCover.N7900.SplitData.node1751 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1752
  · rfl

def B1750 : Block := .branch 169 ![10141204801825835211973625643393, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), B1751, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1750 : B1750.tree = HexagonCover.N7900.SplitData.node1750 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1751
  · rfl
  · rfl

def B1749 : Block := .branch 114 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B1750, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq1749 : B1749.tree = HexagonCover.N7900.SplitData.node1749 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1750
  · rfl

def B1748 : Block := .branch 132 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 432).pointIds 432), (.leaf 5 (Common.fact 177).pointIds 177), B1749]
theorem treeEq1748 : B1748.tree = HexagonCover.N7900.SplitData.node1748 := by
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
  · exact treeEq1749

def B1747 : Block := .branch 68 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 546).pointIds 546), B1748, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 437).pointIds 437)]
theorem treeEq1747 : B1747.tree = HexagonCover.N7900.SplitData.node1747 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1748
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1746 : Block := .branch 133 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 431).pointIds 431), (.leaf 5 (Common.fact 164).pointIds 164), B1747]
theorem treeEq1746 : B1746.tree = HexagonCover.N7900.SplitData.node1746 := by
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
  · exact treeEq1747

def B1745 : Block := .branch 138 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1746, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 430).pointIds 430)]
theorem treeEq1745 : B1745.tree = HexagonCover.N7900.SplitData.node1745 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1746
  · rfl
  · rfl

def B1744 : Block := .branch 144 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1745, (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq1744 : B1744.tree = HexagonCover.N7900.SplitData.node1744 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1745
  · rfl

def B1743 : Block := .branch 124 ![10141205104057290115630919319937, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 545).pointIds 545), (.leaf 1 (Common.fact 142).pointIds 142), (.leaf 2 (Common.fact 143).pointIds 143), (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), B1744]
theorem treeEq1743 : B1743.tree = HexagonCover.N7900.SplitData.node1743 := by
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
  · exact treeEq1744

def B1757 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq1757 : B1757.tree = HexagonCover.N7900.SplitData.node1757 := by
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

def B1756 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1757, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 548).pointIds 548)]
theorem treeEq1756 : B1756.tree = HexagonCover.N7900.SplitData.node1756 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1757
  · rfl
  · rfl

def B1755 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1756, (.leaf 6 (Common.fact 547).pointIds 547)]
theorem treeEq1755 : B1755.tree = HexagonCover.N7900.SplitData.node1755 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1756
  · rfl

def B1742 : Block := .branch 78 ![10141204801825835211973625643393, 309485010541921009104061954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B1743, (.leaf 1 (Common.fact 544).pointIds 544), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1755]
theorem treeEq1742 : B1742.tree = HexagonCover.N7900.SplitData.node1742 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1743
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1755

def B1759 : Block := .branch 133 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 164).pointIds 164), (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq1759 : B1759.tree = HexagonCover.N7900.SplitData.node1759 := by
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

def B1758 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1759, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 506).pointIds 506)]
theorem treeEq1758 : B1758.tree = HexagonCover.N7900.SplitData.node1758 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1759
  · rfl
  · rfl

def B1741 : Block := .branch 69 ![10141204801825835211973625643393, 309485010541921009104061954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] ![B1742, (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 426).pointIds 426), (.leaf 5 (Common.fact 427).pointIds 427), B1758]
theorem treeEq1741 : B1741.tree = HexagonCover.N7900.SplitData.node1741 := by
  change Tree.branch (69 : Fin 170) _ = Tree.branch (69 : Fin 170) _
  apply congrArg (Tree.branch (69 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1742
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1758

theorem accepted1741 : B1741.accepted = true := by decide +kernel
theorem checked1741 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1741 (maskNeeds ![10141204801825835211973625643393, 309485010541921009104061954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1741]
  exact B1741.sound accepted1741
#print axioms checked1741

def Tip1740_1761 : Block := .tip HexagonCover.N7900.SplitData.node1761 ![10143680681904405972523423891841, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] HexagonCover.N7900.SplitAlignedTree.Run0022.checked1761
def Tip1740_1741 : Block := .tip HexagonCover.N7900.SplitData.node1741 ![10141204801825835211973625643393, 309485010541921009104061954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129054217942899091459014720] checked1741
def B1837 : Block := .branch 160 ![385, 374144419156711147060143317477599907935576024679938, 9223512774343137284, 24584, 98320, 393248, 16747336970381226961086085218145912386748480] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq1837 : B1837.tree = HexagonCover.N7900.SplitData.node1837 := by
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

def B1836 : Block := .branch 168 ![42535295865117307932921825928971026817, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 16747336970381226961086085218145912386748480] ![(.leaf 0 (Common.fact 751).pointIds 751), B1837, (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq1836 : B1836.tree = HexagonCover.N7900.SplitData.node1836 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1837
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1835 : Block := .branch 142 ![42535295865117307932921825928971026817, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 5708990770823839524233143877797980545531379744, 11172150670748571175702155649983822010253376] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 630).pointIds 630), (.leaf 5 (Common.fact 496).pointIds 496), B1836]
theorem treeEq1835 : B1835.tree = HexagonCover.N7900.SplitData.node1835 := by
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
  · exact treeEq1836

def B1834 : Block := .branch 78 ![93536104789220322060900947810700854698537828483457, 1538, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 5708990770823839524233143877797980545531379744, 11172150670748571175702155649983822010253376] ![(.leaf 0 (Common.fact 749).pointIds 749), B1835, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1834 : B1834.tree = HexagonCover.N7900.SplitData.node1834 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1835
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1833 : Block := .branch 143 ![93536104789220322060900947810700854698537828483457, 1538, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 5708990770823839524233143877797980545531379744, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 122).pointIds 122), B1834]
theorem treeEq1833 : B1833.tree = HexagonCover.N7900.SplitData.node1833 := by
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
  · exact treeEq1834

def B1832 : Block := .branch 125 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 748294547304193117959810867494614704044382993383456, 21778071483259914419306335004709982044224] ![B1833, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 558).pointIds 558)]
theorem treeEq1832 : B1832.tree = HexagonCover.N7900.SplitData.node1832 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1833
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1831 : Block := .branch 157 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 748294547304193117959810867494614704044382993383456, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1832, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1831 : B1831.tree = HexagonCover.N7900.SplitData.node1831 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1832
  · rfl
  · rfl

def B1830 : Block := .branch 76 ![93536104789177786765035830502767932872608857457025, 442721857769029240322, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 748294547304193117959810867494614704044382993383456, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1831, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq1830 : B1830.tree = HexagonCover.N7900.SplitData.node1830 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1831
  · rfl
  · rfl
  · rfl
  · rfl

def B1829 : Block := .branch 68 ![93536104789177786765035830502767932872608857457025, 147573952589676414466, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 748294547304193117959810867494614704044382993383456, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 748).pointIds 748), B1830, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq1829 : B1829.tree = HexagonCover.N7900.SplitData.node1829 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1830
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1828 : Block := .branch 166 ![1208925819614629174706561, 147573952589676414466, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 748294547304193117959810867494614704044382993383456, 21778071483259914419306335004709982044224] ![B1829, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1828 : B1828.tree = HexagonCover.N7900.SplitData.node1828 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1829
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1827 : Block := .branch 169 ![10141206010751654826602800349569, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 11693440346339929305510536947699713652383843188752, 5708990770823839524233143877797980545531379744, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 559).pointIds 559), B1828, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1827 : B1827.tree = HexagonCover.N7900.SplitData.node1827 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1828
  · rfl

def B1826 : Block := .branch 163 ![10141206010751654826602800349569, 147718067777752270338, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1827, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 619).pointIds 619)]
theorem treeEq1826 : B1826.tree = HexagonCover.N7900.SplitData.node1826 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1827
  · rfl
  · rfl

def B1760 : Block := .branch 91 ![10141206010751654826602800349569, 147718067777752270338, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![Tip1740_1761, (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B1826]
theorem treeEq1760 : B1760.tree = HexagonCover.N7900.SplitData.node1760 := by
  change Tree.branch (91 : Fin 170) _ = Tree.branch (91 : Fin 170) _
  apply congrArg (Tree.branch (91 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1826

def B1740 : Block := .branch 88 ![10141206010751654826602800349569, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 88).pointIds 88), Tip1740_1741, (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1760]
theorem treeEq1740 : B1740.tree = HexagonCover.N7900.SplitData.node1740 := by
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
  · exact treeEq1760

theorem accepted1740 : B1740.accepted = true := by decide +kernel
theorem checked1740 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1740 (maskNeeds ![10141206010751654826602800349569, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1740]
  exact B1740.sound accepted1740
#print axioms checked1740

def B1866 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439882511961511996983048141434015711296] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 760).pointIds 760), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1866 : B1866.tree = HexagonCover.N7900.SplitData.node1866 := by
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

def B1865 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1866]
theorem treeEq1865 : B1865.tree = HexagonCover.N7900.SplitData.node1865 := by
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
  · exact treeEq1866

def B1864 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1865, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1864 : B1864.tree = HexagonCover.N7900.SplitData.node1864 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1865
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1863 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1864, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1863 : B1863.tree = HexagonCover.N7900.SplitData.node1863 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1864
  · rfl
  · rfl

def B1862 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2923003296439877319664653462155419610937686491200] ![B1863, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1862 : B1862.tree = HexagonCover.N7900.SplitData.node1862 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1863
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1861 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 661).pointIds 661), B1862, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1861 : B1861.tree = HexagonCover.N7900.SplitData.node1861 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1862
  · rfl

def B1860 : Block := .branch 142 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), B1861, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1860 : B1860.tree = HexagonCover.N7900.SplitData.node1860 := by
  change Tree.branch (142 : Fin 170) _ = Tree.branch (142 : Fin 170) _
  apply congrArg (Tree.branch (142 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1861
  · rfl
  · rfl

def B1859 : Block := .branch 88 ![10394734921871481092272966284083585, 302231599018845369533954, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B1860]
theorem treeEq1859 : B1859.tree = HexagonCover.N7900.SplitData.node1859 := by
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
  · exact treeEq1860

def B1868 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq1868 : B1868.tree = HexagonCover.N7900.SplitData.node1868 := by
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

def B1867 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1868, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1867 : B1867.tree = HexagonCover.N7900.SplitData.node1867 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1868
  · rfl
  · rfl

def B1858 : Block := .branch 78 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 758).pointIds 758), B1859, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1867]
theorem treeEq1858 : B1858.tree = HexagonCover.N7900.SplitData.node1858 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1859
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1867

def B1875 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439882511961202587531090522279614349376] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq1875 : B1875.tree = HexagonCover.N7900.SplitData.node1875 := by
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

def B1874 : Block := .branch 112 ![42545680458834377588178886921629467009, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 759).pointIds 759), (.leaf 1 (Common.fact 714).pointIds 714), (.leaf 2 (Common.fact 715).pointIds 715), (.leaf 3 (Common.fact 716).pointIds 716), (.leaf 4 (Common.fact 717).pointIds 717), (.leaf 5 (Common.fact 718).pointIds 718), B1875]
theorem treeEq1874 : B1874.tree = HexagonCover.N7900.SplitData.node1874 := by
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
  · exact treeEq1875

def B1873 : Block := .branch 125 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1874, (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1873 : B1873.tree = HexagonCover.N7900.SplitData.node1873 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1874
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1872 : Block := .branch 157 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1873, (.leaf 5 (Common.fact 567).pointIds 567), (.leaf 0 [] 0)]
theorem treeEq1872 : B1872.tree = HexagonCover.N7900.SplitData.node1872 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1873
  · rfl
  · rfl

def B1871 : Block := .branch 166 ![10384593717069655257060992658440577, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 748288838313422294120286634350736906063837462396960, 2923003296439877319664344052703461991783285129280] ![B1872, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 662).pointIds 662)]
theorem treeEq1871 : B1871.tree = HexagonCover.N7900.SplitData.node1871 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1872
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1870 : Block := .branch 169 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 517).pointIds 517), B1871, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1870 : B1870.tree = HexagonCover.N7900.SplitData.node1870 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1871
  · rfl

def B1869 : Block := .branch 143 ![10394734921871481092272966284083585, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B1870, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1869 : B1869.tree = HexagonCover.N7900.SplitData.node1869 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1870
  · rfl
  · rfl

def B1857 : Block := .branch 76 ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 712).pointIds 712), B1858, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B1869]
theorem treeEq1857 : B1857.tree = HexagonCover.N7900.SplitData.node1857 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1858
  · rfl
  · rfl
  · rfl
  · exact treeEq1869

theorem accepted1857 : B1857.accepted = true := by decide +kernel
theorem checked1857 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1857 (maskNeeds ![10394734921871481092272966284083585, 442865972957105096194, 9223512774343137284, 38685626227668133590622216, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1857]
  exact B1857.sound accepted1857
#print axioms checked1857

def Tip1738_1740 : Block := .tip HexagonCover.N7900.SplitData.node1740 ![10141206010751654826602800349569, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked1740
def B1850 : Block := .branch 125 ![467680523945888933825179146469210566289898413752705, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 654).pointIds 654), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1850 : B1850.tree = HexagonCover.N7900.SplitData.node1850 := by
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

def B1849 : Block := .branch 168 ![93536104789177786765035829293842113257979682750849, 1461501637330902918203684833011430924835285370370, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 27222589354626047140998506655015283195968] ![B1850, (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 440).pointIds 440), (.leaf 4 (Common.fact 592).pointIds 592), (.leaf 5 (Common.fact 593).pointIds 593), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq1849 : B1849.tree = HexagonCover.N7900.SplitData.node1849 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1850
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1848 : Block := .branch 160 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 748294547304193117959810867494614704044382993383456, 27222589354626047140998506655015283195968] ![(.leaf 0 (Common.fact 334).pointIds 334), B1849, (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1848 : B1848.tree = HexagonCover.N7900.SplitData.node1848 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1849
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1847 : Block := .branch 132 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9223512774343137284, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 177).pointIds 177), B1848]
theorem treeEq1847 : B1847.tree = HexagonCover.N7900.SplitData.node1847 := by
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
  · exact treeEq1848

def B1846 : Block := .branch 138 ![93536104789177786765035829293842113257979682750849, 295147905179352827394, 9223512774343137284, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 153).pointIds 153), (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), B1847, (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq1846 : B1846.tree = HexagonCover.N7900.SplitData.node1846 := by
  change Tree.branch (138 : Fin 170) _ = Tree.branch (138 : Fin 170) _
  apply congrArg (Tree.branch (138 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1847
  · rfl
  · rfl

def B1845 : Block := .branch 68 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 32667107225361062556412500373923574579264] ![(.leaf 0 (Common.fact 748).pointIds 748), B1846, (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq1845 : B1845.tree = HexagonCover.N7900.SplitData.node1845 := by
  change Tree.branch (68 : Fin 170) _ = Tree.branch (68 : Fin 170) _
  apply congrArg (Tree.branch (68 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1846
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1844 : Block := .branch 133 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), (.leaf 4 (Common.fact 647).pointIds 647), (.leaf 5 (Common.fact 164).pointIds 164), B1845]
theorem treeEq1844 : B1844.tree = HexagonCover.N7900.SplitData.node1844 := by
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
  · exact treeEq1845

def B1843 : Block := .branch 139 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483891031725584512936106991812672] ![(.leaf 0 (Common.fact 641).pointIds 641), (.leaf 1 (Common.fact 642).pointIds 642), (.leaf 2 (Common.fact 643).pointIds 643), (.leaf 3 (Common.fact 644).pointIds 644), B1844, (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq1843 : B1843.tree = HexagonCover.N7900.SplitData.node1843 := by
  change Tree.branch (139 : Fin 170) _ = Tree.branch (139 : Fin 170) _
  apply congrArg (Tree.branch (139 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1844
  · rfl
  · rfl

def B1842 : Block := .branch 99 ![93536104789177786765035830502767932872608857457025, 1538, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 754).pointIds 754), (.leaf 1 (Common.fact 636).pointIds 636), (.leaf 2 (Common.fact 637).pointIds 637), (.leaf 3 (Common.fact 638).pointIds 638), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 640).pointIds 640), B1843]
theorem treeEq1842 : B1842.tree = HexagonCover.N7900.SplitData.node1842 := by
  change Tree.branch (99 : Fin 170) _ = Tree.branch (99 : Fin 170) _
  apply congrArg (Tree.branch (99 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1843

def B1841 : Block := .branch 166 ![1208925819614629174706561, 1538, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 748294547304193117959810867494614704044382993383456, 21778071483257206425470398235358640209984] ![B1842, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 457).pointIds 457), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq1841 : B1841.tree = HexagonCover.N7900.SplitData.node1841 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1842
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1840 : Block := .branch 169 ![10141206010751654826602800349569, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 686).pointIds 686), (.leaf 2 (Common.fact 687).pointIds 687), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 565).pointIds 565), B1841, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq1840 : B1840.tree = HexagonCover.N7900.SplitData.node1840 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1841
  · rfl

def B1839 : Block := .branch 141 ![10141206010751654826602800349569, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B1840, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1839 : B1839.tree = HexagonCover.N7900.SplitData.node1839 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1840
  · rfl
  · rfl

def B1838 : Block := .branch 144 ![10141206010751654826602800349569, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257206425470398235358640209984] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), (.leaf 4 (Common.fact 116).pointIds 116), B1839, (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq1838 : B1838.tree = HexagonCover.N7900.SplitData.node1838 := by
  change Tree.branch (144 : Fin 170) _ = Tree.branch (144 : Fin 170) _
  apply congrArg (Tree.branch (144 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1839
  · rfl

def B1739 : Block := .branch 86 ![10141206010751654826602800349569, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 329).pointIds 329), (.leaf 1 (Common.fact 330).pointIds 330), (.leaf 2 (Common.fact 709).pointIds 709), Tip1738_1740, (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B1838]
theorem treeEq1739 : B1739.tree = HexagonCover.N7900.SplitData.node1739 := by
  change Tree.branch (86 : Fin 170) _ = Tree.branch (86 : Fin 170) _
  apply congrArg (Tree.branch (86 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1838

def B1852 : Block := .branch 142 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 491).pointIds 491), (.leaf 1 (Common.fact 492).pointIds 492), (.leaf 2 (Common.fact 493).pointIds 493), (.leaf 3 (Common.fact 494).pointIds 494), (.leaf 4 (Common.fact 630).pointIds 630), (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1852 : B1852.tree = HexagonCover.N7900.SplitData.node1852 := by
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

def B1851 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B1852, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1851 : B1851.tree = HexagonCover.N7900.SplitData.node1851 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1852
  · rfl
  · rfl

def B1738 : Block := .branch 80 ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B1739, (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), (.leaf 4 (Common.fact 707).pointIds 707), (.leaf 5 (Common.fact 708).pointIds 708), B1851]
theorem treeEq1738 : B1738.tree = HexagonCover.N7900.SplitData.node1738 := by
  change Tree.branch (80 : Fin 170) _ = Tree.branch (80 : Fin 170) _
  apply congrArg (Tree.branch (80 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq1739
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1851

theorem accepted1738 : B1738.accepted = true := by decide +kernel
theorem checked1738 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node1738 (maskNeeds ![10141204801825835211973625643393, 148294528530055693826, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1738]
  exact B1738.sound accepted1738
#print axioms checked1738

end HexagonCover.N7900.SplitAlignedTree.Run0023
