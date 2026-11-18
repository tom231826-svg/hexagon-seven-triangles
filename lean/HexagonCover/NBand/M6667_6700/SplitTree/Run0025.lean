import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0024
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0025
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1784_1820 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1820 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664098140005042819234551690989808356163648] HexagonCover.NBand.M6667_6700.SplitTree.Run0024.checked1820
def Tip1784_1788 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1788 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] HexagonCover.NBand.M6667_6700.SplitTree.Run0024.checked1788
def B1786 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1786 : B1786.tree = HexagonCover.NBand.M6667_6700.SplitData.node1786 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1785 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1786]
theorem treeEq1785 : B1785.tree = HexagonCover.NBand.M6667_6700.SplitData.node1785 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1786

def B1810 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1810 : B1810.tree = HexagonCover.NBand.M6667_6700.SplitData.node1810 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1809 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B1810]
theorem treeEq1809 : B1809.tree = HexagonCover.NBand.M6667_6700.SplitData.node1809 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1810

def B1813 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1813 : B1813.tree = HexagonCover.NBand.M6667_6700.SplitData.node1813 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1812 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1813]
theorem treeEq1812 : B1812.tree = HexagonCover.NBand.M6667_6700.SplitData.node1812 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1813

def B1819 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1819 : B1819.tree = HexagonCover.NBand.M6667_6700.SplitData.node1819 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1818 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1819, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1818 : B1818.tree = HexagonCover.NBand.M6667_6700.SplitData.node1818 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1819
  · rfl
  · rfl

def B1817 : Block := .branch 158 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1193).pointIds 1193), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1818]
theorem treeEq1817 : B1817.tree = HexagonCover.NBand.M6667_6700.SplitData.node1817 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1818

def B1816 : Block := .branch 140 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1817, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1816 : B1816.tree = HexagonCover.NBand.M6667_6700.SplitData.node1816 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1817
  · rfl
  · rfl

def B1815 : Block := .branch 163 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1192).pointIds 1192), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1816]
theorem treeEq1815 : B1815.tree = HexagonCover.NBand.M6667_6700.SplitData.node1815 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1816

def B1814 : Block := .branch 122 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B1815, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip1784_1820]
theorem treeEq1814 : B1814.tree = HexagonCover.NBand.M6667_6700.SplitData.node1814 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1815
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1811 : Block := .branch 121 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1812, (.leaf 5 (Common.fact 430).pointIds 430), B1814]
theorem treeEq1811 : B1811.tree = HexagonCover.NBand.M6667_6700.SplitData.node1811 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1812
  · rfl
  · exact treeEq1814

def B1808 : Block := .branch 120 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1809, (.leaf 5 (Common.fact 163).pointIds 163), B1811]
theorem treeEq1808 : B1808.tree = HexagonCover.NBand.M6667_6700.SplitData.node1808 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1809
  · rfl
  · exact treeEq1811

def B1787 : Block := .branch 79 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![Tip1784_1788, B1808, (.leaf 2 (Common.fact 1184).pointIds 1184), (.leaf 3 (Common.fact 1185).pointIds 1185), (.leaf 4 (Common.fact 1186).pointIds 1186), (.leaf 5 (Common.fact 1187).pointIds 1187), (.leaf 6 (Common.fact 1188).pointIds 1188)]
theorem treeEq1787 : B1787.tree = HexagonCover.NBand.M6667_6700.SplitData.node1787 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1808
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1784 : Block := .branch 119 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1785, (.leaf 5 (Common.fact 419).pointIds 419), B1787]
theorem treeEq1784 : B1784.tree = HexagonCover.NBand.M6667_6700.SplitData.node1784 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1785
  · rfl
  · exact treeEq1787

theorem accepted1784 : B1784.accepted = true := by decide +kernel
theorem checked1784 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1784 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985573511450159696636805184]) := by
  rw [← treeEq1784]
  exact B1784.sound accepted1784
#print axioms checked1784

def Tip1750_1754 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1754 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] HexagonCover.NBand.M6667_6700.SplitTree.Run0024.checked1754
def B1753 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1753 : B1753.tree = HexagonCover.NBand.M6667_6700.SplitData.node1753 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1752 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1753]
theorem treeEq1752 : B1752.tree = HexagonCover.NBand.M6667_6700.SplitData.node1752 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1753

def B1751 : Block := .branch 119 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1752, (.leaf 5 (Common.fact 419).pointIds 419), Tip1750_1754]
theorem treeEq1751 : B1751.tree = HexagonCover.NBand.M6667_6700.SplitData.node1751 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1752
  · rfl
  · rfl

def B1777 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1777 : B1777.tree = HexagonCover.NBand.M6667_6700.SplitData.node1777 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1776 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1777]
theorem treeEq1776 : B1776.tree = HexagonCover.NBand.M6667_6700.SplitData.node1776 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1777

def B1780 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1780 : B1780.tree = HexagonCover.NBand.M6667_6700.SplitData.node1780 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1779 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1780]
theorem treeEq1779 : B1779.tree = HexagonCover.NBand.M6667_6700.SplitData.node1779 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1780

def B1778 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1779, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1778 : B1778.tree = HexagonCover.NBand.M6667_6700.SplitData.node1778 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1779
  · rfl
  · rfl

def B1775 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1776, (.leaf 5 (Common.fact 419).pointIds 419), B1778]
theorem treeEq1775 : B1775.tree = HexagonCover.NBand.M6667_6700.SplitData.node1775 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1776
  · rfl
  · exact treeEq1778

def B1782 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1782 : B1782.tree = HexagonCover.NBand.M6667_6700.SplitData.node1782 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1781 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1782, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1781 : B1781.tree = HexagonCover.NBand.M6667_6700.SplitData.node1781 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1782
  · rfl
  · rfl

def B1774 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1775, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1781]
theorem treeEq1774 : B1774.tree = HexagonCover.NBand.M6667_6700.SplitData.node1774 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1775
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1781

def B1750 : Block := .branch 111 ![590295810358705652097, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![B1751, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B1774]
theorem treeEq1750 : B1750.tree = HexagonCover.NBand.M6667_6700.SplitData.node1750 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1751
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1774

theorem accepted1750 : B1750.accepted = true := by decide +kernel
theorem checked1750 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1750 (maskNeeds ![590295810358705652097, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184]) := by
  rw [← treeEq1750]
  exact B1750.sound accepted1750
#print axioms checked1750

def Tip1744_1784 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1784 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985573511450159696636805184] checked1784
def Tip1744_1750 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1750 ![590295810358705652097, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] checked1750
def B1748 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1010).pointIds 1010)]
theorem treeEq1748 : B1748.tree = HexagonCover.NBand.M6667_6700.SplitData.node1748 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1747 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B1748, (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq1747 : B1747.tree = HexagonCover.NBand.M6667_6700.SplitData.node1747 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1748
  · rfl

def B1746 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387129931434873594290709725248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B1747]
theorem treeEq1746 : B1746.tree = HexagonCover.NBand.M6667_6700.SplitData.node1746 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1747

def B1839 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1839 : B1839.tree = HexagonCover.NBand.M6667_6700.SplitData.node1839 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1838 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1839]
theorem treeEq1838 : B1838.tree = HexagonCover.NBand.M6667_6700.SplitData.node1838 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1839

def B1842 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1842 : B1842.tree = HexagonCover.NBand.M6667_6700.SplitData.node1842 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1841 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1842]
theorem treeEq1841 : B1841.tree = HexagonCover.NBand.M6667_6700.SplitData.node1841 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1842

def B1840 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1841, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1840 : B1840.tree = HexagonCover.NBand.M6667_6700.SplitData.node1840 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1841
  · rfl
  · rfl

def B1837 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1838, (.leaf 5 (Common.fact 419).pointIds 419), B1840]
theorem treeEq1837 : B1837.tree = HexagonCover.NBand.M6667_6700.SplitData.node1837 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1838
  · rfl
  · exact treeEq1840

def B1844 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1844 : B1844.tree = HexagonCover.NBand.M6667_6700.SplitData.node1844 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1843 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1844, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1843 : B1843.tree = HexagonCover.NBand.M6667_6700.SplitData.node1843 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1844
  · rfl
  · rfl

def B1836 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1837, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1843]
theorem treeEq1836 : B1836.tree = HexagonCover.NBand.M6667_6700.SplitData.node1836 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1837
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1843

def B1783 : Block := .branch 111 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![Tip1744_1784, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B1836]
theorem treeEq1783 : B1783.tree = HexagonCover.NBand.M6667_6700.SplitData.node1783 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1836

def B1749 : Block := .branch 69 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![Tip1744_1750, B1783, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1011).pointIds 1011)]
theorem treeEq1749 : B1749.tree = HexagonCover.NBand.M6667_6700.SplitData.node1749 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1783
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1745 : Block := .branch 108 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B1746, (.leaf 5 (Common.fact 136).pointIds 136), B1749]
theorem treeEq1745 : B1745.tree = HexagonCover.NBand.M6667_6700.SplitData.node1745 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1746
  · rfl
  · exact treeEq1749

def B1848 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq1848 : B1848.tree = HexagonCover.NBand.M6667_6700.SplitData.node1848 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1847 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B1848, (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq1847 : B1847.tree = HexagonCover.NBand.M6667_6700.SplitData.node1847 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1848
  · rfl

def B1846 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605831777217696535764533312] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1847]
theorem treeEq1846 : B1846.tree = HexagonCover.NBand.M6667_6700.SplitData.node1846 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1847

def B1845 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820465484124829159846838336] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1846, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq1845 : B1845.tree = HexagonCover.NBand.M6667_6700.SplitData.node1845 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1846
  · rfl
  · rfl

def B1744 : Block := .branch 101 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![B1745, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B1845]
theorem treeEq1744 : B1744.tree = HexagonCover.NBand.M6667_6700.SplitData.node1744 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1745
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1845

theorem accepted1744 : B1744.accepted = true := by decide +kernel
theorem checked1744 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1744 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq1744]
  exact B1744.sound accepted1744
#print axioms checked1744

def Tip1739_1744 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1744 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] checked1744
def B1852 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq1852 : B1852.tree = HexagonCover.NBand.M6667_6700.SplitData.node1852 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1851 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511795441116629495843142850553700679744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), B1852, (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq1851 : B1851.tree = HexagonCover.NBand.M6667_6700.SplitData.node1851 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1852
  · rfl

def B1850 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1851]
theorem treeEq1850 : B1850.tree = HexagonCover.NBand.M6667_6700.SplitData.node1850 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1851

def B1849 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1850, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq1849 : B1849.tree = HexagonCover.NBand.M6667_6700.SplitData.node1849 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1850
  · rfl
  · rfl

def B1743 : Block := .branch 91 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![Tip1739_1744, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B1849]
theorem treeEq1743 : B1743.tree = HexagonCover.NBand.M6667_6700.SplitData.node1743 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1849

def B1856 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq1856 : B1856.tree = HexagonCover.NBand.M6667_6700.SplitData.node1856 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1855 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B1856, (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq1855 : B1855.tree = HexagonCover.NBand.M6667_6700.SplitData.node1855 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1856
  · rfl

def B1854 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923601340401583679807684672] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1855]
theorem treeEq1854 : B1854.tree = HexagonCover.NBand.M6667_6700.SplitData.node1854 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1855

def B1853 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138235047308716303889989696] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1854, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq1853 : B1853.tree = HexagonCover.NBand.M6667_6700.SplitData.node1853 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1854
  · rfl
  · rfl

def B1742 : Block := .branch 89 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 117).pointIds 117), B1743, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B1853]
theorem treeEq1742 : B1742.tree = HexagonCover.NBand.M6667_6700.SplitData.node1742 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1743
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1853

def B1860 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1860 : B1860.tree = HexagonCover.NBand.M6667_6700.SplitData.node1860 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1859 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B1860, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1859 : B1859.tree = HexagonCover.NBand.M6667_6700.SplitData.node1859 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1860
  · rfl

def B1858 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1859]
theorem treeEq1858 : B1858.tree = HexagonCover.NBand.M6667_6700.SplitData.node1858 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1859

def B1857 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1858, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1857 : B1857.tree = HexagonCover.NBand.M6667_6700.SplitData.node1857 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1858
  · rfl
  · rfl

def B1741 : Block := .branch 86 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B1742, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1857]
theorem treeEq1741 : B1741.tree = HexagonCover.NBand.M6667_6700.SplitData.node1741 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1742
  · rfl
  · rfl
  · exact treeEq1857

def B1863 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356890317740949975887586525248] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq1863 : B1863.tree = HexagonCover.NBand.M6667_6700.SplitData.node1863 := by
  change Tree.branch (132 : Fin 173) _ = Tree.branch (132 : Fin 173) _
  apply congrArg (Tree.branch (132 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1862 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070255967004043912050124521536] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1863]
theorem treeEq1862 : B1862.tree = HexagonCover.NBand.M6667_6700.SplitData.node1862 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1863

def B1861 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321144470600710951044674206826560] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1862, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq1861 : B1861.tree = HexagonCover.NBand.M6667_6700.SplitData.node1861 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1862
  · rfl
  · rfl

def B1740 : Block := .branch 85 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B1741, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B1861]
theorem treeEq1740 : B1740.tree = HexagonCover.NBand.M6667_6700.SplitData.node1740 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1741
  · rfl
  · rfl
  · exact treeEq1861

def B1739 : Block := .branch 137 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B1740, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq1739 : B1739.tree = HexagonCover.NBand.M6667_6700.SplitData.node1739 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1740
  · rfl
  · rfl

theorem accepted1739 : B1739.accepted = true := by decide +kernel
theorem checked1739 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1739 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq1739]
  exact B1739.sound accepted1739
#print axioms checked1739

end HexagonCover.NBand.M6667_6700.SplitTree.Run0025
