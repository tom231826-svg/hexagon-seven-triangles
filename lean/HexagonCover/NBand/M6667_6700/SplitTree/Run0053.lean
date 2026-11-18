import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0041
import HexagonCover.NBand.M6667_6700.SplitTree.Run0051
import HexagonCover.NBand.M6667_6700.SplitTree.Run0052
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0053
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3706_3710 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3710 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] HexagonCover.NBand.M6667_6700.SplitTree.Run0052.checked3710
def B3816 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1870722095783555735301033498527046896463107262513216] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 1212).pointIds 1212), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1213).pointIds 1213)]
theorem treeEq3816 : B3816.tree = HexagonCover.NBand.M6667_6700.SplitData.node3816 := by
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

def B3815 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 1394477139642005823272909141255386130645008, 187072209578355573530071658587684226515959365894176, 374144419156711147060460229825573084335432338505792] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 738).pointIds 738), B3816]
theorem treeEq3815 : B3815.tree = HexagonCover.NBand.M6667_6700.SplitData.node3815 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3816

def B3814 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 1394477139642005823272909141255386130645008, 393248, 374875169975376599818270112175752247678632738684992] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 1210).pointIds 1210), B3815, (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3814 : B3814.tree = HexagonCover.NBand.M6667_6700.SplitData.node3814 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3815
  · rfl

def B3813 : Block := .branch 129 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374875169975376599818270112175752247678632738684992] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B3814, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 1209).pointIds 1209)]
theorem treeEq3813 : B3813.tree = HexagonCover.NBand.M6667_6700.SplitData.node3813 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3814
  · rfl
  · rfl

def B3812 : Block := .branch 139 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374875169975376599818270112175752247678632738684992] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B3813, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1208).pointIds 1208)]
theorem treeEq3812 : B3812.tree = HexagonCover.NBand.M6667_6700.SplitData.node3812 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3813
  · rfl
  · rfl

def B3811 : Block := .branch 106 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374875169975376599818270112175752247678632738684992] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B3812, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1207).pointIds 1207)]
theorem treeEq3811 : B3811.tree = HexagonCover.NBand.M6667_6700.SplitData.node3811 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3812
  · rfl
  · rfl
  · rfl

def B3810 : Block := .branch 117 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 6361185876482754952780563186981647496189332434714688] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B3811, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1206).pointIds 1206)]
theorem treeEq3810 : B3810.tree = HexagonCover.NBand.M6667_6700.SplitData.node3810 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3811
  · rfl
  · rfl
  · rfl

def B3809 : Block := .branch 140 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6361185876482754952780563186981647496189332434714688] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3810, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1205).pointIds 1205)]
theorem treeEq3809 : B3809.tree = HexagonCover.NBand.M6667_6700.SplitData.node3809 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3810
  · rfl
  · rfl

def B3709 : Block := .branch 67 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563186981499922236742758301760] ![(.leaf 0 (Common.fact 73).pointIds 73), Tip3706_3710, (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), B3809]
theorem treeEq3709 : B3709.tree = HexagonCover.NBand.M6667_6700.SplitData.node3709 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3809

def B3819 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452758126795000273114182271750373440] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1322).pointIds 1322)]
theorem treeEq3819 : B3819.tree = HexagonCover.NBand.M6667_6700.SplitData.node3819 := by
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

def B3818 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270112175641567214190481375296] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3819, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3818 : B3818.tree = HexagonCover.NBand.M6667_6700.SplitData.node3818 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3819
  · rfl
  · rfl

def B3817 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270112175641567214190481375296] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3818, (.leaf 6 (Common.fact 1321).pointIds 1321)]
theorem treeEq3817 : B3817.tree = HexagonCover.NBand.M6667_6700.SplitData.node3817 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3818
  · rfl

def B3708 : Block := .branch 65 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563186981499922236742758301760] ![(.leaf 0 (Common.fact 68).pointIds 68), (.leaf 1 (Common.fact 69).pointIds 69), B3709, (.leaf 3 (Common.fact 70).pointIds 70), (.leaf 4 (Common.fact 71).pointIds 71), (.leaf 5 (Common.fact 72).pointIds 72), B3817]
theorem treeEq3708 : B3708.tree = HexagonCover.NBand.M6667_6700.SplitData.node3708 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3709
  · rfl
  · rfl
  · rfl
  · exact treeEq3817

def B3707 : Block := .branch 83 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 1256).pointIds 1256), B3708, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq3707 : B3707.tree = HexagonCover.NBand.M6667_6700.SplitData.node3707 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3708
  · rfl
  · rfl
  · rfl

def B3822 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452758126795000254667438198040821824] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1324).pointIds 1324)]
theorem treeEq3822 : B3822.tree = HexagonCover.NBand.M6667_6700.SplitData.node3822 := by
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

def B3821 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270112175623120470116771823680] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3822, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3821 : B3821.tree = HexagonCover.NBand.M6667_6700.SplitData.node3821 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3822
  · rfl
  · rfl

def B3820 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270112175623120470116771823680] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3821, (.leaf 6 (Common.fact 1323).pointIds 1323)]
theorem treeEq3820 : B3820.tree = HexagonCover.NBand.M6667_6700.SplitData.node3820 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3821
  · rfl

def B3706 : Block := .branch 64 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816] ![(.leaf 0 (Common.fact 63).pointIds 63), (.leaf 1 (Common.fact 64).pointIds 64), B3707, (.leaf 3 (Common.fact 65).pointIds 65), (.leaf 4 (Common.fact 66).pointIds 66), (.leaf 5 (Common.fact 67).pointIds 67), B3820]
theorem treeEq3706 : B3706.tree = HexagonCover.NBand.M6667_6700.SplitData.node3706 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3707
  · rfl
  · rfl
  · rfl
  · exact treeEq3820

theorem accepted3706 : B3706.accepted = true := by decide +kernel
theorem checked3706 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3706 (maskNeeds ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816]) := by
  rw [← treeEq3706]
  exact B3706.sound accepted3706
#print axioms checked3706

def Tip2983_2986 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2986 ![1152921504606847361, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0051.checked2986
def Tip2983_3706 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3706 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816] checked3706
def B3699 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1222).pointIds 1222)]
theorem treeEq3699 : B3699.tree = HexagonCover.NBand.M6667_6700.SplitData.node3699 := by
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

def B3698 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3699, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1221).pointIds 1221)]
theorem treeEq3698 : B3698.tree = HexagonCover.NBand.M6667_6700.SplitData.node3698 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3699
  · rfl
  · rfl

def B3697 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 5986310706507378354261318027389782551067032915804224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3698, (.leaf 6 (Common.fact 1220).pointIds 1220)]
theorem treeEq3697 : B3697.tree = HexagonCover.NBand.M6667_6700.SplitData.node3697 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3698
  · rfl

def B2985 : Block := .branch 63 ![1152921504606847361, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 58).pointIds 58), (.leaf 1 (Common.fact 59).pointIds 59), Tip2983_2986, (.leaf 3 (Common.fact 60).pointIds 60), (.leaf 4 (Common.fact 61).pointIds 61), (.leaf 5 (Common.fact 62).pointIds 62), B3697]
theorem treeEq2985 : B2985.tree = HexagonCover.NBand.M6667_6700.SplitData.node2985 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3697

def B3702 : Block := .branch 119 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 699).pointIds 699), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1225).pointIds 1225)]
theorem treeEq3702 : B3702.tree = HexagonCover.NBand.M6667_6700.SplitData.node3702 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3701 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3702, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1224).pointIds 1224)]
theorem treeEq3701 : B3701.tree = HexagonCover.NBand.M6667_6700.SplitData.node3701 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3702
  · rfl
  · rfl

def B3700 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 5986310706507378354261318027389777939381014488416320] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3701, (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq3700 : B3700.tree = HexagonCover.NBand.M6667_6700.SplitData.node3700 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3701
  · rfl

def B2984 : Block := .branch 62 ![1152921504606847361, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 53).pointIds 53), (.leaf 1 (Common.fact 54).pointIds 54), B2985, (.leaf 3 (Common.fact 55).pointIds 55), (.leaf 4 (Common.fact 56).pointIds 56), (.leaf 5 (Common.fact 57).pointIds 57), B3700]
theorem treeEq2984 : B2984.tree = HexagonCover.NBand.M6667_6700.SplitData.node2984 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2985
  · rfl
  · rfl
  · rfl
  · exact treeEq3700

def B3825 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452758126795000245444066161186046016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1326).pointIds 1326)]
theorem treeEq3825 : B3825.tree = HexagonCover.NBand.M6667_6700.SplitData.node3825 := by
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

def B3824 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270112175613897098079917047872] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3825, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3824 : B3824.tree = HexagonCover.NBand.M6667_6700.SplitData.node3824 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3825
  · rfl
  · rfl

def B3823 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270112175613897098079917047872] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3824, (.leaf 6 (Common.fact 1325).pointIds 1325)]
theorem treeEq3823 : B3823.tree = HexagonCover.NBand.M6667_6700.SplitData.node3823 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3824
  · rfl

def B3705 : Block := .branch 63 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816] ![(.leaf 0 (Common.fact 58).pointIds 58), (.leaf 1 (Common.fact 59).pointIds 59), Tip2983_3706, (.leaf 3 (Common.fact 60).pointIds 60), (.leaf 4 (Common.fact 61).pointIds 61), (.leaf 5 (Common.fact 62).pointIds 62), B3823]
theorem treeEq3705 : B3705.tree = HexagonCover.NBand.M6667_6700.SplitData.node3705 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3823

def B3828 : Block := .branch 119 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452758126795000240832380142758658112] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 699).pointIds 699), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1328).pointIds 1328)]
theorem treeEq3828 : B3828.tree = HexagonCover.NBand.M6667_6700.SplitData.node3828 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3827 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270112175609285412061489659968] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3828, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3827 : B3827.tree = HexagonCover.NBand.M6667_6700.SplitData.node3827 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3828
  · rfl
  · rfl

def B3826 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270112175609285412061489659968] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3827, (.leaf 6 (Common.fact 1327).pointIds 1327)]
theorem treeEq3826 : B3826.tree = HexagonCover.NBand.M6667_6700.SplitData.node3826 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3827
  · rfl

def B3704 : Block := .branch 62 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6361185876482754952780563496466509743581811483082816] ![(.leaf 0 (Common.fact 53).pointIds 53), (.leaf 1 (Common.fact 54).pointIds 54), B3705, (.leaf 3 (Common.fact 55).pointIds 55), (.leaf 4 (Common.fact 56).pointIds 56), (.leaf 5 (Common.fact 57).pointIds 57), B3826]
theorem treeEq3704 : B3704.tree = HexagonCover.NBand.M6667_6700.SplitData.node3704 := by
  change Tree.branch (62 : Fin 173) _ = Tree.branch (62 : Fin 173) _
  apply congrArg (Tree.branch (62 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3705
  · rfl
  · rfl
  · rfl
  · exact treeEq3826

def B3703 : Block := .branch 159 ![385, 1297036692682704386, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1304).pointIds 1304), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B3704]
theorem treeEq3703 : B3703.tree = HexagonCover.NBand.M6667_6700.SplitData.node3703 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3704

def B2983 : Block := .branch 60 ![385, 144115188075857410, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![B2984, B3703, (.leaf 2 (Common.fact 49).pointIds 49), (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 0 [] 0)]
theorem treeEq2983 : B2983.tree = HexagonCover.NBand.M6667_6700.SplitData.node2983 := by
  change Tree.branch (60 : Fin 173) _ = Tree.branch (60 : Fin 173) _
  apply congrArg (Tree.branch (60 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2984
  · exact treeEq3703
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2983 : B2983.accepted = true := by decide +kernel
theorem checked2983 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2983 (maskNeeds ![385, 144115188075857410, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2983]
  exact B2983.sound accepted2983
#print axioms checked2983

def Tip2968_2983 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2983 ![385, 144115188075857410, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked2983
def B2980 : Block := .branch 119 ![385, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 374144419156711148358534444761511446371713714487360] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1168).pointIds 1168)]
theorem treeEq2980 : B2980.tree = HexagonCover.NBand.M6667_6700.SplitData.node2980 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2979 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148358534444761511446371713714487360] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B2980, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1167).pointIds 1167)]
theorem treeEq2979 : B2979.tree = HexagonCover.NBand.M6667_6700.SplitData.node2979 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2980
  · rfl
  · rfl

def B2978 : Block := .branch 67 ![385, 70368744179202, 1099511633924, 24584, 98320, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 73).pointIds 73), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), B2979]
theorem treeEq2978 : B2978.tree = HexagonCover.NBand.M6667_6700.SplitData.node2978 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2979

def B2977 : Block := .branch 78 ![385, 70368744179202, 1099511633924, 24584, 98320, 393248, 374144419156711148358534444459132417515466744397888] ![(.leaf 0 (Common.fact 87).pointIds 87), (.leaf 1 (Common.fact 1252).pointIds 1252), (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2978]
theorem treeEq2977 : B2977.tree = HexagonCover.NBand.M6667_6700.SplitData.node2977 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2978

def B2976 : Block := .branch 89 ![385, 70368744179202, 1099511633924, 24584, 98320, 393248, 374144419156711148358534444459132417515466744397888] ![(.leaf 0 (Common.fact 117).pointIds 117), (.leaf 1 (Common.fact 1251).pointIds 1251), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B2977]
theorem treeEq2976 : B2976.tree = HexagonCover.NBand.M6667_6700.SplitData.node2976 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2977

def B2975 : Block := .branch 159 ![385, 70368744179202, 1099511633924, 24584, 98320, 393248, 374144419156711148358534444459132417515466744397888] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1249).pointIds 1249), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B2976]
theorem treeEq2975 : B2975.tree = HexagonCover.NBand.M6667_6700.SplitData.node2975 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2976

def B3830 : Block := .branch 119 ![385, 1538, 6148, 24584, 748288838313422294120286634350736906063837462102032, 393248, 374144419156711148359168269759246676331403171856448] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1330).pointIds 1330)]
theorem treeEq3830 : B3830.tree = HexagonCover.NBand.M6667_6700.SplitData.node3830 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3829 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168269759246676331403171856448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3830, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1329).pointIds 1329)]
theorem treeEq3829 : B3829.tree = HexagonCover.NBand.M6667_6700.SplitData.node3829 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3830
  · rfl
  · rfl

def B2982 : Block := .branch 57 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 44).pointIds 44), Tip2968_2983, (.leaf 2 (Common.fact 45).pointIds 45), (.leaf 3 (Common.fact 46).pointIds 46), (.leaf 4 (Common.fact 47).pointIds 47), (.leaf 5 (Common.fact 48).pointIds 48), B3829]
theorem treeEq2982 : B2982.tree = HexagonCover.NBand.M6667_6700.SplitData.node2982 := by
  change Tree.branch (57 : Fin 173) _ = Tree.branch (57 : Fin 173) _
  apply congrArg (Tree.branch (57 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3829

def B3833 : Block := .branch 119 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148359168269759246532497690072711232] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), (.leaf 4 (Common.fact 699).pointIds 699), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 1333).pointIds 1333)]
theorem treeEq3833 : B3833.tree = HexagonCover.NBand.M6667_6700.SplitData.node3833 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3832 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168269759246532497690072711232] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3833, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1332).pointIds 1332)]
theorem treeEq3832 : B3832.tree = HexagonCover.NBand.M6667_6700.SplitData.node3832 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3833
  · rfl
  · rfl

def B3831 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168269759246532497690072711232] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3832, (.leaf 6 (Common.fact 1331).pointIds 1331)]
theorem treeEq3831 : B3831.tree = HexagonCover.NBand.M6667_6700.SplitData.node3831 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3832
  · rfl

def B2981 : Block := .branch 48 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 34).pointIds 34), B2982, (.leaf 2 (Common.fact 35).pointIds 35), (.leaf 3 (Common.fact 36).pointIds 36), (.leaf 4 (Common.fact 37).pointIds 37), (.leaf 5 (Common.fact 38).pointIds 38), B3831]
theorem treeEq2981 : B2981.tree = HexagonCover.NBand.M6667_6700.SplitData.node2981 := by
  change Tree.branch (48 : Fin 173) _ = Tree.branch (48 : Fin 173) _
  apply congrArg (Tree.branch (48 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2982
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3831

def B2974 : Block := .branch 46 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 1155).pointIds 1155), B2975, B2981, (.leaf 3 (Common.fact 1156).pointIds 1156), (.leaf 4 (Common.fact 1157).pointIds 1157), (.leaf 5 (Common.fact 1158).pointIds 1158), (.leaf 6 (Common.fact 1159).pointIds 1159)]
theorem treeEq2974 : B2974.tree = HexagonCover.NBand.M6667_6700.SplitData.node2974 := by
  change Tree.branch (46 : Fin 173) _ = Tree.branch (46 : Fin 173) _
  apply congrArg (Tree.branch (46 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2975
  · exact treeEq2981
  · rfl
  · rfl
  · rfl
  · rfl

def B2973 : Block := .branch 105 ![385, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 845).pointIds 845), (.leaf 1 (Common.fact 846).pointIds 846), (.leaf 2 (Common.fact 847).pointIds 847), B2974, (.leaf 4 (Common.fact 848).pointIds 848), (.leaf 5 (Common.fact 849).pointIds 849), (.leaf 6 (Common.fact 1154).pointIds 1154)]
theorem treeEq2973 : B2973.tree = HexagonCover.NBand.M6667_6700.SplitData.node2973 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2974
  · rfl
  · rfl
  · rfl

def B2972 : Block := .branch 148 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 390).pointIds 390), (.leaf 1 (Common.fact 391).pointIds 391), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), B2973, (.leaf 5 (Common.fact 394).pointIds 394), (.leaf 6 (Common.fact 994).pointIds 994)]
theorem treeEq2972 : B2972.tree = HexagonCover.NBand.M6667_6700.SplitData.node2972 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2973
  · rfl
  · rfl

def B2971 : Block := .branch 172 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 1150).pointIds 1150), (.leaf 1 (Common.fact 1247).pointIds 1247), (.leaf 2 (Common.fact 1248).pointIds 1248), (.leaf 3 (Common.fact 1153).pointIds 1153), (.leaf 4 (Common.fact 993).pointIds 993), (.leaf 5 (Common.fact 896).pointIds 896), B2972]
theorem treeEq2971 : B2971.tree = HexagonCover.NBand.M6667_6700.SplitData.node2971 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2972

def B2970 : Block := .branch 92 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![B2971, (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 835).pointIds 835), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 988).pointIds 988)]
theorem treeEq2970 : B2970.tree = HexagonCover.NBand.M6667_6700.SplitData.node2970 := by
  change Tree.branch (92 : Fin 173) _ = Tree.branch (92 : Fin 173) _
  apply congrArg (Tree.branch (92 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2971
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2969 : Block := .branch 134 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 408).pointIds 408), (.leaf 1 (Common.fact 409).pointIds 409), (.leaf 2 (Common.fact 410).pointIds 410), (.leaf 3 (Common.fact 411).pointIds 411), (.leaf 4 (Common.fact 412).pointIds 412), B2970, (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq2969 : B2969.tree = HexagonCover.NBand.M6667_6700.SplitData.node2969 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2970
  · rfl

def B2968 : Block := .branch 143 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 398).pointIds 398), (.leaf 3 (Common.fact 399).pointIds 399), (.leaf 4 (Common.fact 400).pointIds 400), B2969, (.leaf 6 (Common.fact 986).pointIds 986)]
theorem treeEq2968 : B2968.tree = HexagonCover.NBand.M6667_6700.SplitData.node2968 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2969
  · rfl

theorem accepted2968 : B2968.accepted = true := by decide +kernel
theorem checked2968 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2968 (maskNeeds ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632]) := by
  rw [← treeEq2968]
  exact B2968.sound accepted2968
#print axioms checked2968

def Tip0000_0007 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0007 ![385, 1099511629314, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] HexagonCover.NBand.M6667_6700.SplitTree.Run0041.checked0007
def Tip0000_2968 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2968 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] checked2968
def B2965 : Block := .branch 122 ![11692013098647223345629478661730264157247460344193, 1538, 6148, 24584, 98320, 393248, 1299024952583878079465771341709376] ![(.leaf 0 (Common.fact 1241).pointIds 1241), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 1244).pointIds 1244)]
theorem treeEq2965 : B2965.tree = HexagonCover.NBand.M6667_6700.SplitData.node2965 := by
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

def B2964 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1299024952583878079465771341709376] ![B2965, (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), (.leaf 6 (Common.fact 1243).pointIds 1243)]
theorem treeEq2964 : B2964.tree = HexagonCover.NBand.M6667_6700.SplitData.node2964 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2965
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 48 ![385, 1099511629314, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 34).pointIds 34), Tip0000_0007, (.leaf 2 (Common.fact 35).pointIds 35), (.leaf 3 (Common.fact 36).pointIds 36), (.leaf 4 (Common.fact 37).pointIds 37), (.leaf 5 (Common.fact 38).pointIds 38), B2964]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M6667_6700.SplitData.node0006 := by
  change Tree.branch (48 : Fin 173) _ = Tree.branch (48 : Fin 173) _
  apply congrArg (Tree.branch (48 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2964

def B2967 : Block := .branch 147 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168579244256353561283820781632] ![(.leaf 0 (Common.fact 980).pointIds 980), (.leaf 1 (Common.fact 981).pointIds 981), (.leaf 2 (Common.fact 982).pointIds 982), (.leaf 3 (Common.fact 983).pointIds 983), Tip0000_2968, (.leaf 5 (Common.fact 984).pointIds 984), (.leaf 6 (Common.fact 985).pointIds 985)]
theorem treeEq2967 : B2967.tree = HexagonCover.NBand.M6667_6700.SplitData.node2967 := by
  change Tree.branch (147 : Fin 173) _ = Tree.branch (147 : Fin 173) _
  apply congrArg (Tree.branch (147 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2966 : Block := .branch 168 ![385, 1538, 1099511633924, 24584, 98320, 393248, 1299025262068887900529365089779776] ![(.leaf 0 (Common.fact 1146).pointIds 1146), (.leaf 1 (Common.fact 1245).pointIds 1245), (.leaf 2 (Common.fact 1246).pointIds 1246), (.leaf 3 (Common.fact 1149).pointIds 1149), (.leaf 4 (Common.fact 389).pointIds 389), (.leaf 5 (Common.fact 318).pointIds 318), B2967]
theorem treeEq2966 : B2966.tree = HexagonCover.NBand.M6667_6700.SplitData.node2966 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2967

def B0005 : Block := .branch 40 ![385, 1538, 6148, 24584, 98320, 393248, 1299025416811392811201899452170304] ![(.leaf 0 (Common.fact 30).pointIds 30), B0006, B2966, (.leaf 3 (Common.fact 31).pointIds 31), (.leaf 4 (Common.fact 32).pointIds 32), (.leaf 5 (Common.fact 33).pointIds 33), (.leaf 0 [] 0)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M6667_6700.SplitData.node0005 := by
  change Tree.branch (40 : Fin 173) _ = Tree.branch (40 : Fin 173) _
  apply congrArg (Tree.branch (40 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0006
  · exact treeEq2966
  · rfl
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 951202177685904069275369865280] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), (.leaf 2 (Common.fact 26).pointIds 26), (.leaf 3 (Common.fact 27).pointIds 27), (.leaf 4 (Common.fact 28).pointIds 28), (.leaf 5 (Common.fact 29).pointIds 29), B0005]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M6667_6700.SplitData.node0004 := by
  change Tree.branch (110 : Fin 173) _ = Tree.branch (110 : Fin 173) _
  apply congrArg (Tree.branch (110 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0005

def B0003 : Block := .branch 99 ![385, 1538, 6148, 24584, 98320, 393248, 317376877571789368527018262592] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), (.leaf 3 (Common.fact 21).pointIds 21), (.leaf 4 (Common.fact 22).pointIds 22), (.leaf 5 (Common.fact 23).pointIds 23), B0004]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M6667_6700.SplitData.node0003 := by
  change Tree.branch (99 : Fin 173) _ = Tree.branch (99 : Fin 173) _
  apply congrArg (Tree.branch (99 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0004

def B0002 : Block := .branch 98 ![385, 1538, 6148, 24584, 98320, 393248, 464227514732018152842461248] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M6667_6700.SplitData.node0002 := by
  change Tree.branch (98 : Fin 173) _ = Tree.branch (98 : Fin 173) _
  apply congrArg (Tree.branch (98 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 88 ![385, 1538, 6148, 24584, 98320, 393248, 154742504910673084117680192] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M6667_6700.SplitData.node0001 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 87 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M6667_6700.SplitData.node0000 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M6667_6700.SplitTree.Run0053
