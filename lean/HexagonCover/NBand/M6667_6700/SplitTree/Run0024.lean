import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0024
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1710 : Block := .branch 122 ![11692013098647223345629478661731417078752067191169, 1538, 6148, 24584, 98320, 393248, 5846006549326270129440443947744099111147977310272] ![(.leaf 0 (Common.fact 806).pointIds 806), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 1143).pointIds 1143)]
theorem treeEq1710 : B1710.tree = HexagonCover.NBand.M6667_6700.SplitData.node1710 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1709 : Block := .branch 163 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 5846006549326270129440443947744099111147977310272] ![B1710, (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq1709 : B1709.tree = HexagonCover.NBand.M6667_6700.SplitData.node1709 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1710
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1708 : Block := .branch 162 ![1152921504606847361, 1538, 6148, 24584, 4704063440315053318917690573136763755266064, 393248, 2658456625704616878967032524247138368] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 1141).pointIds 1141), (.leaf 5 (Common.fact 227).pointIds 227), B1709]
theorem treeEq1708 : B1708.tree = HexagonCover.NBand.M6667_6700.SplitData.node1708 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1709

def B1707 : Block := .branch 164 ![1152921504606847361, 1538, 6148, 24584, 4704063440315053318917690573136763755266064, 393248, 2658456625704616878967032524247138368] ![(.leaf 0 (Common.fact 228).pointIds 228), (.leaf 1 (Common.fact 229).pointIds 229), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 1140).pointIds 1140), B1708, (.leaf 0 [] 0)]
theorem treeEq1707 : B1707.tree = HexagonCover.NBand.M6667_6700.SplitData.node1707 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1708
  · rfl

def B1706 : Block := .branch 166 ![1152921504606847361, 1538, 6148, 24584, 4704063440315053318917690573136763755266064, 393248, 2658456625704616878967032524247138368] ![(.leaf 0 (Common.fact 300).pointIds 300), (.leaf 1 (Common.fact 301).pointIds 301), (.leaf 2 (Common.fact 302).pointIds 302), (.leaf 3 (Common.fact 303).pointIds 303), (.leaf 4 (Common.fact 1139).pointIds 1139), B1707, (.leaf 6 (Common.fact 305).pointIds 305)]
theorem treeEq1706 : B1706.tree = HexagonCover.NBand.M6667_6700.SplitData.node1706 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1707
  · rfl

def B1705 : Block := .branch 141 ![1152921504606847361, 1538, 6148, 24584, 1916470290498725426225725789055718567018512, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), B1706, (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 1138).pointIds 1138)]
theorem treeEq1705 : B1705.tree = HexagonCover.NBand.M6667_6700.SplitData.node1705 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1706
  · rfl
  · rfl

def B1704 : Block := .branch 137 ![1152921504606847361, 1538, 6148, 79228162514264337593543974920, 1742245718635204932932477990050653242753040, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 1136).pointIds 1136), B1705, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 1137).pointIds 1137)]
theorem treeEq1704 : B1704.tree = HexagonCover.NBand.M6667_6700.SplitData.node1704 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1705
  · rfl
  · rfl

def B1703 : Block := .branch 138 ![1152921504606847361, 1538, 6148, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 1134).pointIds 1134), B1704, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 1135).pointIds 1135)]
theorem treeEq1703 : B1703.tree = HexagonCover.NBand.M6667_6700.SplitData.node1703 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1704
  · rfl
  · rfl

def B1702 : Block := .branch 96 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 1128).pointIds 1128), (.leaf 1 (Common.fact 1129).pointIds 1129), (.leaf 2 (Common.fact 1130).pointIds 1130), B1703, (.leaf 4 (Common.fact 1131).pointIds 1131), (.leaf 5 (Common.fact 1132).pointIds 1132), (.leaf 6 (Common.fact 1133).pointIds 1133)]
theorem treeEq1702 : B1702.tree = HexagonCover.NBand.M6667_6700.SplitData.node1702 := by
  change Tree.branch (96 : Fin 173) _ = Tree.branch (96 : Fin 173) _
  apply congrArg (Tree.branch (96 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1703
  · rfl
  · rfl
  · rfl

def B1701 : Block := .branch 106 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B1702, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1127).pointIds 1127)]
theorem treeEq1701 : B1701.tree = HexagonCover.NBand.M6667_6700.SplitData.node1701 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1702
  · rfl
  · rfl
  · rfl

def B1700 : Block := .branch 117 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 10889035741470030830827987437816583159840, 2659755016831900642931515522505244736] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B1701, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1126).pointIds 1126)]
theorem treeEq1700 : B1700.tree = HexagonCover.NBand.M6667_6700.SplitData.node1700 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1701
  · rfl
  · rfl
  · rfl

def B1699 : Block := .branch 121 ![1152921504606847361, 1538, 6148, 24584, 715714541215342186448661958312808352082657296, 10889035741470030830827987437816583159840, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 1110).pointIds 1110), (.leaf 5 (Common.fact 430).pointIds 430), B1700]
theorem treeEq1699 : B1699.tree = HexagonCover.NBand.M6667_6700.SplitData.node1699 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1700

def B1698 : Block := .branch 149 ![1152921504606847361, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 10889035741470030830827987437816583159840, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B1699, (.leaf 5 (Common.fact 208).pointIds 208), (.leaf 6 (Common.fact 1125).pointIds 1125)]
theorem treeEq1698 : B1698.tree = HexagonCover.NBand.M6667_6700.SplitData.node1698 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1699
  · rfl
  · rfl

def B1697 : Block := .branch 133 ![1152921504606847361, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), B1698, (.leaf 6 (Common.fact 1124).pointIds 1124)]
theorem treeEq1697 : B1697.tree = HexagonCover.NBand.M6667_6700.SplitData.node1697 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1698
  · rfl

def B1696 : Block := .branch 134 ![1152921504606847361, 1538, 6148, 24584, 2090694862362245919518973588060783891283984, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B1697, (.leaf 6 (Common.fact 1123).pointIds 1123)]
theorem treeEq1696 : B1696.tree = HexagonCover.NBand.M6667_6700.SplitData.node1696 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1697
  · rfl

def B1695 : Block := .branch 139 ![1152921504606847361, 1538, 6148, 24584, 1393796574908163946345982392040522594222096, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B1696, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1122).pointIds 1122)]
theorem treeEq1695 : B1695.tree = HexagonCover.NBand.M6667_6700.SplitData.node1695 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1696
  · rfl
  · rfl

def B1694 : Block := .branch 140 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1695, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1121).pointIds 1121)]
theorem treeEq1694 : B1694.tree = HexagonCover.NBand.M6667_6700.SplitData.node1694 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1695
  · rfl
  · rfl

def B1693 : Block := .branch 143 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B1694, (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq1693 : B1693.tree = HexagonCover.NBand.M6667_6700.SplitData.node1693 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1694
  · rfl

def B1692 : Block := .branch 148 ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068897123901401944555584] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B1693, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq1692 : B1692.tree = HexagonCover.NBand.M6667_6700.SplitData.node1692 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1693
  · rfl
  · rfl

theorem accepted1692 : B1692.accepted = true := by decide +kernel
theorem checked1692 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1692 (maskNeeds ![1152921504606847361, 1538, 6148, 24584, 98320, 393248, 1299025262068897123901401944555584]) := by
  rw [← treeEq1692]
  exact B1692.sound accepted1692
#print axioms checked1692

def B1756 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1756 : B1756.tree = HexagonCover.NBand.M6667_6700.SplitData.node1756 := by
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

def B1755 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B1756]
theorem treeEq1755 : B1755.tree = HexagonCover.NBand.M6667_6700.SplitData.node1755 := by
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
  · exact treeEq1756

def B1759 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1759 : B1759.tree = HexagonCover.NBand.M6667_6700.SplitData.node1759 := by
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

def B1758 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1759]
theorem treeEq1758 : B1758.tree = HexagonCover.NBand.M6667_6700.SplitData.node1758 := by
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
  · exact treeEq1759

def B1765 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1765 : B1765.tree = HexagonCover.NBand.M6667_6700.SplitData.node1765 := by
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

def B1764 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1765, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1764 : B1764.tree = HexagonCover.NBand.M6667_6700.SplitData.node1764 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1765
  · rfl
  · rfl

def B1763 : Block := .branch 158 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1181).pointIds 1181), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1764]
theorem treeEq1763 : B1763.tree = HexagonCover.NBand.M6667_6700.SplitData.node1763 := by
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
  · exact treeEq1764

def B1762 : Block := .branch 140 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1763, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1762 : B1762.tree = HexagonCover.NBand.M6667_6700.SplitData.node1762 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1763
  · rfl
  · rfl

def B1761 : Block := .branch 163 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1180).pointIds 1180), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1762]
theorem treeEq1761 : B1761.tree = HexagonCover.NBand.M6667_6700.SplitData.node1761 := by
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
  · exact treeEq1762

def B1770 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1770 : B1770.tree = HexagonCover.NBand.M6667_6700.SplitData.node1770 := by
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

def B1769 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1770, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1769 : B1769.tree = HexagonCover.NBand.M6667_6700.SplitData.node1769 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1770
  · rfl
  · rfl

def B1768 : Block := .branch 158 ![10636420114708594987340532089113018753, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1183).pointIds 1183), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1769]
theorem treeEq1768 : B1768.tree = HexagonCover.NBand.M6667_6700.SplitData.node1768 := by
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
  · exact treeEq1769

def B1773 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1773 : B1773.tree = HexagonCover.NBand.M6667_6700.SplitData.node1773 := by
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

def B1772 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1773]
theorem treeEq1772 : B1772.tree = HexagonCover.NBand.M6667_6700.SplitData.node1772 := by
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
  · exact treeEq1773

def B1771 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1772, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1771 : B1771.tree = HexagonCover.NBand.M6667_6700.SplitData.node1771 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1772
  · rfl
  · rfl

def B1767 : Block := .branch 123 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1768, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1771]
theorem treeEq1767 : B1767.tree = HexagonCover.NBand.M6667_6700.SplitData.node1767 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1771

def B1766 : Block := .branch 140 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1767, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1766 : B1766.tree = HexagonCover.NBand.M6667_6700.SplitData.node1766 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1767
  · rfl
  · rfl

def B1760 : Block := .branch 122 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B1761, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B1766]
theorem treeEq1760 : B1760.tree = HexagonCover.NBand.M6667_6700.SplitData.node1760 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1761
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1766

def B1757 : Block := .branch 121 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1758, (.leaf 5 (Common.fact 430).pointIds 430), B1760]
theorem treeEq1757 : B1757.tree = HexagonCover.NBand.M6667_6700.SplitData.node1757 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1758
  · rfl
  · exact treeEq1760

def B1754 : Block := .branch 120 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1755, (.leaf 5 (Common.fact 163).pointIds 163), B1757]
theorem treeEq1754 : B1754.tree = HexagonCover.NBand.M6667_6700.SplitData.node1754 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1755
  · rfl
  · exact treeEq1757

theorem accepted1754 : B1754.accepted = true := by decide +kernel
theorem checked1754 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1754 (maskNeeds ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216]) := by
  rw [← treeEq1754]
  exact B1754.sound accepted1754
#print axioms checked1754

def B1825 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1825 : B1825.tree = HexagonCover.NBand.M6667_6700.SplitData.node1825 := by
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

def B1824 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1825, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1824 : B1824.tree = HexagonCover.NBand.M6667_6700.SplitData.node1824 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1825
  · rfl
  · rfl

def B1823 : Block := .branch 158 ![10636420115946534436330102005306491265, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1199).pointIds 1199), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1824]
theorem treeEq1823 : B1823.tree = HexagonCover.NBand.M6667_6700.SplitData.node1823 := by
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
  · exact treeEq1824

def B1828 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1828 : B1828.tree = HexagonCover.NBand.M6667_6700.SplitData.node1828 := by
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

def B1827 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1828]
theorem treeEq1827 : B1827.tree = HexagonCover.NBand.M6667_6700.SplitData.node1827 := by
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
  · exact treeEq1828

def B1826 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1827, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1826 : B1826.tree = HexagonCover.NBand.M6667_6700.SplitData.node1826 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1827
  · rfl
  · rfl

def B1822 : Block := .branch 123 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1823, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1826]
theorem treeEq1822 : B1822.tree = HexagonCover.NBand.M6667_6700.SplitData.node1822 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1823
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1826

def B1832 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1832 : B1832.tree = HexagonCover.NBand.M6667_6700.SplitData.node1832 := by
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

def B1831 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1832, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1831 : B1831.tree = HexagonCover.NBand.M6667_6700.SplitData.node1831 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1832
  · rfl
  · rfl

def B1830 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1831]
theorem treeEq1830 : B1830.tree = HexagonCover.NBand.M6667_6700.SplitData.node1830 := by
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
  · exact treeEq1831

def B1835 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1835 : B1835.tree = HexagonCover.NBand.M6667_6700.SplitData.node1835 := by
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

def B1834 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1835]
theorem treeEq1834 : B1834.tree = HexagonCover.NBand.M6667_6700.SplitData.node1834 := by
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
  · exact treeEq1835

def B1833 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1834, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1833 : B1833.tree = HexagonCover.NBand.M6667_6700.SplitData.node1833 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1834
  · rfl
  · rfl

def B1829 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1830, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1833]
theorem treeEq1829 : B1829.tree = HexagonCover.NBand.M6667_6700.SplitData.node1829 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1830
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1833

def B1821 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![B1822, B1829, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq1821 : B1821.tree = HexagonCover.NBand.M6667_6700.SplitData.node1821 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1822
  · exact treeEq1829
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1820 : Block := .branch 140 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1821, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1820 : B1820.tree = HexagonCover.NBand.M6667_6700.SplitData.node1820 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1821
  · rfl
  · rfl

theorem accepted1820 : B1820.accepted = true := by decide +kernel
theorem checked1820 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1820 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq1820]
  exact B1820.sound accepted1820
#print axioms checked1820

def B1790 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1790 : B1790.tree = HexagonCover.NBand.M6667_6700.SplitData.node1790 := by
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

def B1789 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B1790]
theorem treeEq1789 : B1789.tree = HexagonCover.NBand.M6667_6700.SplitData.node1789 := by
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
  · exact treeEq1790

def B1793 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1793 : B1793.tree = HexagonCover.NBand.M6667_6700.SplitData.node1793 := by
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

def B1792 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1793]
theorem treeEq1792 : B1792.tree = HexagonCover.NBand.M6667_6700.SplitData.node1792 := by
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
  · exact treeEq1793

def B1799 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1799 : B1799.tree = HexagonCover.NBand.M6667_6700.SplitData.node1799 := by
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

def B1798 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1799, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1798 : B1798.tree = HexagonCover.NBand.M6667_6700.SplitData.node1798 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1799
  · rfl
  · rfl

def B1797 : Block := .branch 158 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1190).pointIds 1190), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1798]
theorem treeEq1797 : B1797.tree = HexagonCover.NBand.M6667_6700.SplitData.node1797 := by
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
  · exact treeEq1798

def B1796 : Block := .branch 140 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1797, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1796 : B1796.tree = HexagonCover.NBand.M6667_6700.SplitData.node1796 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1797
  · rfl
  · rfl

def B1795 : Block := .branch 163 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1189).pointIds 1189), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1796]
theorem treeEq1795 : B1795.tree = HexagonCover.NBand.M6667_6700.SplitData.node1795 := by
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
  · exact treeEq1796

def B1804 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1804 : B1804.tree = HexagonCover.NBand.M6667_6700.SplitData.node1804 := by
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

def B1803 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1804, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1803 : B1803.tree = HexagonCover.NBand.M6667_6700.SplitData.node1803 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1804
  · rfl
  · rfl

def B1802 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1803]
theorem treeEq1802 : B1802.tree = HexagonCover.NBand.M6667_6700.SplitData.node1802 := by
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
  · exact treeEq1803

def B1807 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1807 : B1807.tree = HexagonCover.NBand.M6667_6700.SplitData.node1807 := by
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

def B1806 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1807]
theorem treeEq1806 : B1806.tree = HexagonCover.NBand.M6667_6700.SplitData.node1806 := by
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
  · exact treeEq1807

def B1805 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1806, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1805 : B1805.tree = HexagonCover.NBand.M6667_6700.SplitData.node1805 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1806
  · rfl
  · rfl

def B1801 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1802, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1805]
theorem treeEq1801 : B1801.tree = HexagonCover.NBand.M6667_6700.SplitData.node1801 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1802
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1805

def B1800 : Block := .branch 140 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1801, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1800 : B1800.tree = HexagonCover.NBand.M6667_6700.SplitData.node1800 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1801
  · rfl
  · rfl

def B1794 : Block := .branch 122 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B1795, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B1800]
theorem treeEq1794 : B1794.tree = HexagonCover.NBand.M6667_6700.SplitData.node1794 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1795
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1800

def B1791 : Block := .branch 121 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1792, (.leaf 5 (Common.fact 430).pointIds 430), B1794]
theorem treeEq1791 : B1791.tree = HexagonCover.NBand.M6667_6700.SplitData.node1791 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1792
  · rfl
  · exact treeEq1794

def B1788 : Block := .branch 120 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1789, (.leaf 5 (Common.fact 163).pointIds 163), B1791]
theorem treeEq1788 : B1788.tree = HexagonCover.NBand.M6667_6700.SplitData.node1788 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1789
  · rfl
  · exact treeEq1791

theorem accepted1788 : B1788.accepted = true := by decide +kernel
theorem checked1788 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1788 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324373021175280070756401216]) := by
  rw [← treeEq1788]
  exact B1788.sound accepted1788
#print axioms checked1788

end HexagonCover.NBand.M6667_6700.SplitTree.Run0024
