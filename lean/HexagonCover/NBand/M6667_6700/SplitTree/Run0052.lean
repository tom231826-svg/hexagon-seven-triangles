import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0051
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0052
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3712_3724 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3724 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] HexagonCover.NBand.M6667_6700.SplitTree.Run0051.checked3724
def B3717 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892640482531892634672657256441970752] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1306).pointIds 1306)]
theorem treeEq3717 : B3717.tree = HexagonCover.NBand.M6667_6700.SplitData.node3717 := by
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

def B3716 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598520195897541897766593418979967040] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3717]
theorem treeEq3716 : B3716.tree = HexagonCover.NBand.M6667_6700.SplitData.node3716 := by
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
  · exact treeEq3717

def B3715 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3716, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3715 : B3715.tree = HexagonCover.NBand.M6667_6700.SplitData.node3715 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3716
  · rfl
  · rfl

def B3720 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757809901692992277177816950767680] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1309).pointIds 1309)]
theorem treeEq3720 : B3720.tree = HexagonCover.NBand.M6667_6700.SplitData.node3720 := by
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

def B3719 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131518417787560109857570880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3720, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3719 : B3719.tree = HexagonCover.NBand.M6667_6700.SplitData.node3719 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3720
  · rfl
  · rfl

def B3718 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131518417787560109857570880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3719, (.leaf 6 (Common.fact 1307).pointIds 1307)]
theorem treeEq3718 : B3718.tree = HexagonCover.NBand.M6667_6700.SplitData.node3718 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3719
  · rfl

def B3714 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3715, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3718]
theorem treeEq3714 : B3714.tree = HexagonCover.NBand.M6667_6700.SplitData.node3714 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3715
  · rfl
  · rfl
  · exact treeEq3718

def B3723 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374875169975376599817636288084416378639923885375552] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1311).pointIds 1311)]
theorem treeEq3723 : B3723.tree = HexagonCover.NBand.M6667_6700.SplitData.node3723 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3722 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113384530493340672236978240] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3723, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3722 : B3722.tree = HexagonCover.NBand.M6667_6700.SplitData.node3722 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3723
  · rfl
  · rfl

def B3721 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113384530493340672236978240] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3722, (.leaf 6 (Common.fact 1310).pointIds 1310)]
theorem treeEq3721 : B3721.tree = HexagonCover.NBand.M6667_6700.SplitData.node3721 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3722
  · rfl

def B3713 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![B3714, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3721]
theorem treeEq3713 : B3713.tree = HexagonCover.NBand.M6667_6700.SplitData.node3713 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3714
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3721

def B3712 : Block := .branch 78 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 87).pointIds 87), B3713, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip3712_3724]
theorem treeEq3712 : B3712.tree = HexagonCover.NBand.M6667_6700.SplitData.node3712 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3713
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3712 : B3712.accepted = true := by decide +kernel
theorem checked3712 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3712 (maskNeeds ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064]) := by
  rw [← treeEq3712]
  exact B3712.sound accepted3712
#print axioms checked3712

def B3778 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892639848706894752012860165384044608] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1313).pointIds 1313)]
theorem treeEq3778 : B3778.tree = HexagonCover.NBand.M6667_6700.SplitData.node3778 := by
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

def B3777 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598519562072544015106796327922040896] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3778]
theorem treeEq3777 : B3777.tree = HexagonCover.NBand.M6667_6700.SplitData.node3777 := by
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
  · exact treeEq3778

def B3776 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3777, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3776 : B3776.tree = HexagonCover.NBand.M6667_6700.SplitData.node3776 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3777
  · rfl
  · rfl

def B3781 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757176076695109617380725892841536] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1315).pointIds 1315)]
theorem treeEq3781 : B3781.tree = HexagonCover.NBand.M6667_6700.SplitData.node3781 := by
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

def B3780 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131820649242463767151247424] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3781, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3780 : B3780.tree = HexagonCover.NBand.M6667_6700.SplitData.node3780 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3781
  · rfl
  · rfl

def B3779 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131820649242463767151247424] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3780, (.leaf 6 (Common.fact 1314).pointIds 1314)]
theorem treeEq3779 : B3779.tree = HexagonCover.NBand.M6667_6700.SplitData.node3779 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3780
  · rfl

def B3775 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3776, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3779]
theorem treeEq3775 : B3775.tree = HexagonCover.NBand.M6667_6700.SplitData.node3775 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3776
  · rfl
  · rfl
  · exact treeEq3779

def B3784 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374875169975376599817636288386647833543581179052096] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1317).pointIds 1317)]
theorem treeEq3784 : B3784.tree = HexagonCover.NBand.M6667_6700.SplitData.node3784 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3783 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113686761948244329530654784] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3784, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3783 : B3783.tree = HexagonCover.NBand.M6667_6700.SplitData.node3783 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3784
  · rfl
  · rfl

def B3782 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113686761948244329530654784] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3783, (.leaf 6 (Common.fact 1316).pointIds 1316)]
theorem treeEq3782 : B3782.tree = HexagonCover.NBand.M6667_6700.SplitData.node3782 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3783
  · rfl

def B3774 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![B3775, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3782]
theorem treeEq3774 : B3774.tree = HexagonCover.NBand.M6667_6700.SplitData.node3774 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3775
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3782

def B3773 : Block := .branch 95 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3774, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1312).pointIds 1312)]
theorem treeEq3773 : B3773.tree = HexagonCover.NBand.M6667_6700.SplitData.node3773 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3774
  · rfl
  · rfl
  · rfl

theorem accepted3773 : B3773.accepted = true := by decide +kernel
theorem checked3773 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3773 (maskNeeds ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608]) := by
  rw [← treeEq3773]
  exact B3773.sound accepted3773
#print axioms checked3773

def B3802 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3802 : B3802.tree = HexagonCover.NBand.M6667_6700.SplitData.node3802 := by
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

def B3801 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3802]
theorem treeEq3801 : B3801.tree = HexagonCover.NBand.M6667_6700.SplitData.node3801 := by
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
  · exact treeEq3802

def B3800 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3801, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3800 : B3800.tree = HexagonCover.NBand.M6667_6700.SplitData.node3800 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3801
  · rfl
  · rfl

def B3805 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3805 : B3805.tree = HexagonCover.NBand.M6667_6700.SplitData.node3805 := by
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

def B3804 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131896207106189681474666560] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3805, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3804 : B3804.tree = HexagonCover.NBand.M6667_6700.SplitData.node3804 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3805
  · rfl
  · rfl

def B3803 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131896207106189681474666560] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3804, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3803 : B3803.tree = HexagonCover.NBand.M6667_6700.SplitData.node3803 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3804
  · rfl

def B3799 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3800, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3803]
theorem treeEq3799 : B3799.tree = HexagonCover.NBand.M6667_6700.SplitData.node3799 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3800
  · rfl
  · rfl
  · exact treeEq3803

def B3808 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3808 : B3808.tree = HexagonCover.NBand.M6667_6700.SplitData.node3808 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3807 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3808, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3807 : B3807.tree = HexagonCover.NBand.M6667_6700.SplitData.node3807 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3808
  · rfl
  · rfl

def B3806 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3807, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3806 : B3806.tree = HexagonCover.NBand.M6667_6700.SplitData.node3806 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3807
  · rfl

def B3798 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![B3799, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3806]
theorem treeEq3798 : B3798.tree = HexagonCover.NBand.M6667_6700.SplitData.node3798 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3799
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3806

def B3797 : Block := .branch 95 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3798, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3797 : B3797.tree = HexagonCover.NBand.M6667_6700.SplitData.node3797 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3798
  · rfl
  · rfl
  · rfl

theorem accepted3797 : B3797.accepted = true := by decide +kernel
theorem checked3797 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3797 (maskNeeds ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744]) := by
  rw [← treeEq3797]
  exact B3797.sound accepted3797
#print axioms checked3797

def Tip3761_3773 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3773 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] checked3773
def B3766 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892640482531892634672657256441970752] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1306).pointIds 1306)]
theorem treeEq3766 : B3766.tree = HexagonCover.NBand.M6667_6700.SplitData.node3766 := by
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

def B3765 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598520195897541897766593418979967040] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3766]
theorem treeEq3765 : B3765.tree = HexagonCover.NBand.M6667_6700.SplitData.node3765 := by
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
  · exact treeEq3766

def B3764 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3765, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3764 : B3764.tree = HexagonCover.NBand.M6667_6700.SplitData.node3764 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3765
  · rfl
  · rfl

def B3769 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757809901692992277177816950767680] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1309).pointIds 1309)]
theorem treeEq3769 : B3769.tree = HexagonCover.NBand.M6667_6700.SplitData.node3769 := by
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

def B3768 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131518417787560109857570880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3769, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3768 : B3768.tree = HexagonCover.NBand.M6667_6700.SplitData.node3768 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3769
  · rfl
  · rfl

def B3767 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131518417787560109857570880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3768, (.leaf 6 (Common.fact 1307).pointIds 1307)]
theorem treeEq3767 : B3767.tree = HexagonCover.NBand.M6667_6700.SplitData.node3767 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3768
  · rfl

def B3763 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3764, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3767]
theorem treeEq3763 : B3763.tree = HexagonCover.NBand.M6667_6700.SplitData.node3763 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3764
  · rfl
  · rfl
  · exact treeEq3767

def B3772 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374875169975376599817636288084416378639923885375552] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1311).pointIds 1311)]
theorem treeEq3772 : B3772.tree = HexagonCover.NBand.M6667_6700.SplitData.node3772 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3771 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113384530493340672236978240] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3772, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3771 : B3771.tree = HexagonCover.NBand.M6667_6700.SplitData.node3771 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3772
  · rfl
  · rfl

def B3770 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113384530493340672236978240] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3771, (.leaf 6 (Common.fact 1310).pointIds 1310)]
theorem treeEq3770 : B3770.tree = HexagonCover.NBand.M6667_6700.SplitData.node3770 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3771
  · rfl

def B3762 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![B3763, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3770]
theorem treeEq3762 : B3762.tree = HexagonCover.NBand.M6667_6700.SplitData.node3762 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3763
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3770

def B3761 : Block := .branch 78 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 87).pointIds 87), B3762, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip3761_3773]
theorem treeEq3761 : B3761.tree = HexagonCover.NBand.M6667_6700.SplitData.node3761 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3762
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3761 : B3761.accepted = true := by decide +kernel
theorem checked3761 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3761 (maskNeeds ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064]) := by
  rw [← treeEq3761]
  exact B3761.sound accepted3761
#print axioms checked3761

def Tip3711_3748 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3748 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] HexagonCover.NBand.M6667_6700.SplitTree.Run0051.checked3748
def Tip3711_3712 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3712 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] checked3712
def B3741 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892640482531968192536383170765389888] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1318).pointIds 1318)]
theorem treeEq3741 : B3741.tree = HexagonCover.NBand.M6667_6700.SplitData.node3741 := by
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

def B3740 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598520195897617455630319333303386176] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3741]
theorem treeEq3740 : B3740.tree = HexagonCover.NBand.M6667_6700.SplitData.node3740 := by
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
  · exact treeEq3741

def B3739 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3740, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3739 : B3739.tree = HexagonCover.NBand.M6667_6700.SplitData.node3739 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3740
  · rfl
  · rfl

def B3744 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757809901768550140903731274186816] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1320).pointIds 1320)]
theorem treeEq3744 : B3744.tree = HexagonCover.NBand.M6667_6700.SplitData.node3744 := by
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

def B3743 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131593975651286024180990016] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3744, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3743 : B3743.tree = HexagonCover.NBand.M6667_6700.SplitData.node3743 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3744
  · rfl
  · rfl

def B3742 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131593975651286024180990016] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3743, (.leaf 6 (Common.fact 1319).pointIds 1319)]
theorem treeEq3742 : B3742.tree = HexagonCover.NBand.M6667_6700.SplitData.node3742 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3743
  · rfl

def B3738 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3739, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3742]
theorem treeEq3738 : B3738.tree = HexagonCover.NBand.M6667_6700.SplitData.node3738 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3739
  · rfl
  · rfl
  · exact treeEq3742

def B3747 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3747 : B3747.tree = HexagonCover.NBand.M6667_6700.SplitData.node3747 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3746 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3747, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3746 : B3746.tree = HexagonCover.NBand.M6667_6700.SplitData.node3746 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3747
  · rfl
  · rfl

def B3745 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3746, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3745 : B3745.tree = HexagonCover.NBand.M6667_6700.SplitData.node3745 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3746
  · rfl

def B3737 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![B3738, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3745]
theorem treeEq3737 : B3737.tree = HexagonCover.NBand.M6667_6700.SplitData.node3737 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3738
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3745

def B3736 : Block := .branch 78 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 87).pointIds 87), B3737, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip3711_3748]
theorem treeEq3736 : B3736.tree = HexagonCover.NBand.M6667_6700.SplitData.node3736 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3737
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3711 : Block := .branch 76 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip3711_3712, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B3736]
theorem treeEq3711 : B3711.tree = HexagonCover.NBand.M6667_6700.SplitData.node3711 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3736

theorem accepted3711 : B3711.accepted = true := by decide +kernel
theorem checked3711 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3711 (maskNeeds ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064]) := by
  rw [← treeEq3711]
  exact B3711.sound accepted3711
#print axioms checked3711

def Tip3710_3797 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3797 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] checked3797
def Tip3710_3761 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3761 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] checked3761
def Tip3710_3711 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3711 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] checked3711
def B3790 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892640482531968192536383170765389888] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1318).pointIds 1318)]
theorem treeEq3790 : B3790.tree = HexagonCover.NBand.M6667_6700.SplitData.node3790 := by
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

def B3789 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598520195897617455630319333303386176] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3790]
theorem treeEq3789 : B3789.tree = HexagonCover.NBand.M6667_6700.SplitData.node3789 := by
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
  · exact treeEq3790

def B3788 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3789, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3788 : B3788.tree = HexagonCover.NBand.M6667_6700.SplitData.node3788 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3789
  · rfl
  · rfl

def B3793 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757809901768550140903731274186816] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1320).pointIds 1320)]
theorem treeEq3793 : B3793.tree = HexagonCover.NBand.M6667_6700.SplitData.node3793 := by
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

def B3792 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131593975651286024180990016] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3793, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3792 : B3792.tree = HexagonCover.NBand.M6667_6700.SplitData.node3792 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3793
  · rfl
  · rfl

def B3791 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131593975651286024180990016] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3792, (.leaf 6 (Common.fact 1319).pointIds 1319)]
theorem treeEq3791 : B3791.tree = HexagonCover.NBand.M6667_6700.SplitData.node3791 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3792
  · rfl

def B3787 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3788, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3791]
theorem treeEq3787 : B3787.tree = HexagonCover.NBand.M6667_6700.SplitData.node3787 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3788
  · rfl
  · rfl
  · exact treeEq3791

def B3796 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3796 : B3796.tree = HexagonCover.NBand.M6667_6700.SplitData.node3796 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3795 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3796, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3795 : B3795.tree = HexagonCover.NBand.M6667_6700.SplitData.node3795 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3796
  · rfl
  · rfl

def B3794 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3795, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3794 : B3794.tree = HexagonCover.NBand.M6667_6700.SplitData.node3794 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3795
  · rfl

def B3786 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![B3787, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3794]
theorem treeEq3786 : B3786.tree = HexagonCover.NBand.M6667_6700.SplitData.node3786 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3787
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3794

def B3785 : Block := .branch 78 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112251162537451957385691200] ![(.leaf 0 (Common.fact 87).pointIds 87), B3786, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), Tip3710_3797]
theorem treeEq3785 : B3785.tree = HexagonCover.NBand.M6667_6700.SplitData.node3785 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3786
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3760 : Block := .branch 76 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip3710_3761, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B3785]
theorem treeEq3760 : B3760.tree = HexagonCover.NBand.M6667_6700.SplitData.node3760 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3785

def B3710 : Block := .branch 71 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), Tip3710_3711, B3760, (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 0 [] 0)]
theorem treeEq3710 : B3710.tree = HexagonCover.NBand.M6667_6700.SplitData.node3710 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3760
  · rfl
  · rfl
  · rfl

theorem accepted3710 : B3710.accepted = true := by decide +kernel
theorem checked3710 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3710 (maskNeeds ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112175604673726043062272064]) := by
  rw [← treeEq3710]
  exact B3710.sound accepted3710
#print axioms checked3710

end HexagonCover.NBand.M6667_6700.SplitTree.Run0052
