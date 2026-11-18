import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0046
import HexagonCover.NBand.M6667_6700.SplitTree.Run0050
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0051
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2991_3149 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3149 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] HexagonCover.NBand.M6667_6700.SplitTree.Run0046.checked3149
def Tip2991_2992 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2992 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0046.checked2992
def B3340 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3340 : B3340.tree = HexagonCover.NBand.M6667_6700.SplitData.node3340 := by
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

def B3339 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3340]
theorem treeEq3339 : B3339.tree = HexagonCover.NBand.M6667_6700.SplitData.node3339 := by
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
  · exact treeEq3340

def B3338 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444836921736145038361493568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3339, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3338 : B3338.tree = HexagonCover.NBand.M6667_6700.SplitData.node3338 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3339
  · rfl
  · rfl

def B3343 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3343 : B3343.tree = HexagonCover.NBand.M6667_6700.SplitData.node3343 := by
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

def B3342 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3343, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3342 : B3342.tree = HexagonCover.NBand.M6667_6700.SplitData.node3342 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3343
  · rfl
  · rfl

def B3341 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3342, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3341 : B3341.tree = HexagonCover.NBand.M6667_6700.SplitData.node3341 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3342
  · rfl

def B3337 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3338, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3341]
theorem treeEq3337 : B3337.tree = HexagonCover.NBand.M6667_6700.SplitData.node3337 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3338
  · rfl
  · rfl
  · exact treeEq3341

def B3346 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3346 : B3346.tree = HexagonCover.NBand.M6667_6700.SplitData.node3346 := by
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

def B3345 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3346, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3345 : B3345.tree = HexagonCover.NBand.M6667_6700.SplitData.node3345 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3346
  · rfl
  · rfl

def B3344 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3345, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3344 : B3344.tree = HexagonCover.NBand.M6667_6700.SplitData.node3344 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3345
  · rfl

def B3336 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![B3337, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3344]
theorem treeEq3336 : B3336.tree = HexagonCover.NBand.M6667_6700.SplitData.node3336 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3337
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3344

def B3335 : Block := .branch 95 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3336, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3335 : B3335.tree = HexagonCover.NBand.M6667_6700.SplitData.node3335 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3336
  · rfl
  · rfl
  · rfl

def B3148 : Block := .branch 78 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 87).pointIds 87), Tip2991_3149, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B3335]
theorem treeEq3148 : B3148.tree = HexagonCover.NBand.M6667_6700.SplitData.node3148 := by
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
  · exact treeEq3335

def B2991 : Block := .branch 76 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip2991_2992, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B3148]
theorem treeEq2991 : B2991.tree = HexagonCover.NBand.M6667_6700.SplitData.node2991 := by
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
  · exact treeEq3148

theorem accepted2991 : B2991.accepted = true := by decide +kernel
theorem checked2991 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2991 (maskNeeds ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2991]
  exact B2991.sound accepted2991
#print axioms checked2991

def Tip2990_3520 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3520 ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] HexagonCover.NBand.M6667_6700.SplitTree.Run0050.checked3520
def Tip2990_3348 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3348 ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0050.checked3348
def Tip2990_2991 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2991 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked2991
def B3676 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3676 : B3676.tree = HexagonCover.NBand.M6667_6700.SplitData.node3676 := by
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

def B3675 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3676]
theorem treeEq3675 : B3675.tree = HexagonCover.NBand.M6667_6700.SplitData.node3675 := by
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
  · exact treeEq3676

def B3674 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444836921736145038361493568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3675, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq3674 : B3674.tree = HexagonCover.NBand.M6667_6700.SplitData.node3674 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3675
  · rfl
  · rfl

def B3679 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3679 : B3679.tree = HexagonCover.NBand.M6667_6700.SplitData.node3679 := by
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

def B3678 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3679, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3678 : B3678.tree = HexagonCover.NBand.M6667_6700.SplitData.node3678 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3679
  · rfl
  · rfl

def B3677 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461364285744213190553204424768] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3678, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3677 : B3677.tree = HexagonCover.NBand.M6667_6700.SplitData.node3677 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3678
  · rfl

def B3673 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3674, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3677]
theorem treeEq3673 : B3673.tree = HexagonCover.NBand.M6667_6700.SplitData.node3673 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3674
  · rfl
  · rfl
  · exact treeEq3677

def B3682 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3682 : B3682.tree = HexagonCover.NBand.M6667_6700.SplitData.node3682 := by
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

def B3681 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3682, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3681 : B3681.tree = HexagonCover.NBand.M6667_6700.SplitData.node3681 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3682
  · rfl
  · rfl

def B3680 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3681, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3680 : B3680.tree = HexagonCover.NBand.M6667_6700.SplitData.node3680 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3681
  · rfl

def B3672 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![B3673, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3680]
theorem treeEq3672 : B3672.tree = HexagonCover.NBand.M6667_6700.SplitData.node3672 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3673
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3680

def B3671 : Block := .branch 95 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344942931099356486409125952] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3672, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3671 : B3671.tree = HexagonCover.NBand.M6667_6700.SplitData.node3671 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3672
  · rfl
  · rfl
  · rfl

def B3519 : Block := .branch 78 ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 87).pointIds 87), Tip2990_3520, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B3671]
theorem treeEq3519 : B3519.tree = HexagonCover.NBand.M6667_6700.SplitData.node3519 := by
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
  · exact treeEq3671

def B3347 : Block := .branch 76 ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), Tip2990_3348, (.leaf 3 (Common.fact 84).pointIds 84), (.leaf 4 (Common.fact 85).pointIds 85), (.leaf 5 (Common.fact 86).pointIds 86), B3519]
theorem treeEq3347 : B3347.tree = HexagonCover.NBand.M6667_6700.SplitData.node3347 := by
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
  · exact treeEq3519

def B2990 : Block := .branch 71 ![1152921504606847361, 1538, 55340233320640288772, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), Tip2990_2991, B3347, (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 0 [] 0)]
theorem treeEq2990 : B2990.tree = HexagonCover.NBand.M6667_6700.SplitData.node2990 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3347
  · rfl
  · rfl
  · rfl

theorem accepted2990 : B2990.accepted = true := by decide +kernel
theorem checked2990 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2990 (maskNeeds ![1152921504606847361, 1538, 55340233320640288772, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2990]
  exact B2990.sound accepted2990
#print axioms checked2990

def Tip2986_2990 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2990 ![1152921504606847361, 1538, 55340233320640288772, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] checked2990
def B3690 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394477139642005823272909141255386130645008, 393248, 1870722095783555735301033498527046896463107262513216] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 1212).pointIds 1212), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1213).pointIds 1213)]
theorem treeEq3690 : B3690.tree = HexagonCover.NBand.M6667_6700.SplitData.node3690 := by
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

def B3689 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 1394477139642005823272909141255386130645008, 187072209578355573530071658587684226515959365894176, 374144419156711147060460229825573084335432338505792] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), (.leaf 5 (Common.fact 738).pointIds 738), B3690]
theorem treeEq3689 : B3689.tree = HexagonCover.NBand.M6667_6700.SplitData.node3689 := by
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
  · exact treeEq3690

def B3688 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 1394477139642005823272909141255386130645008, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 1210).pointIds 1210), B3689, (.leaf 6 (Common.fact 1211).pointIds 1211)]
theorem treeEq3688 : B3688.tree = HexagonCover.NBand.M6667_6700.SplitData.node3688 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3689
  · rfl

def B3687 : Block := .branch 129 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), B3688, (.leaf 5 (Common.fact 559).pointIds 559), (.leaf 6 (Common.fact 1209).pointIds 1209)]
theorem treeEq3687 : B3687.tree = HexagonCover.NBand.M6667_6700.SplitData.node3687 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3688
  · rfl
  · rfl

def B3686 : Block := .branch 139 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B3687, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 1208).pointIds 1208)]
theorem treeEq3686 : B3686.tree = HexagonCover.NBand.M6667_6700.SplitData.node3686 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3687
  · rfl
  · rfl

def B3685 : Block := .branch 106 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 374144419156711148359168269759394106168804772413504] ![(.leaf 0 (Common.fact 1058).pointIds 1058), (.leaf 1 (Common.fact 1059).pointIds 1059), (.leaf 2 (Common.fact 1060).pointIds 1060), B3686, (.leaf 4 (Common.fact 1061).pointIds 1061), (.leaf 5 (Common.fact 1062).pointIds 1062), (.leaf 6 (Common.fact 1207).pointIds 1207)]
theorem treeEq3685 : B3685.tree = HexagonCover.NBand.M6667_6700.SplitData.node3685 := by
  change Tree.branch (106 : Fin 173) _ = Tree.branch (106 : Fin 173) _
  apply congrArg (Tree.branch (106 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3686
  · rfl
  · rfl
  · rfl

def B3684 : Block := .branch 117 ![385, 1538, 1099511633924, 24584, 1393796574908163946345982392040522594222096, 393248, 6360455125664089501321461344565289354679504468443200] ![(.leaf 0 (Common.fact 777).pointIds 777), (.leaf 1 (Common.fact 778).pointIds 778), (.leaf 2 (Common.fact 779).pointIds 779), B3685, (.leaf 4 (Common.fact 1056).pointIds 1056), (.leaf 5 (Common.fact 781).pointIds 781), (.leaf 6 (Common.fact 1206).pointIds 1206)]
theorem treeEq3684 : B3684.tree = HexagonCover.NBand.M6667_6700.SplitData.node3684 := by
  change Tree.branch (117 : Fin 173) _ = Tree.branch (117 : Fin 173) _
  apply congrArg (Tree.branch (117 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3685
  · rfl
  · rfl
  · rfl

def B3683 : Block := .branch 140 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461344565289354679504468443200] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B3684, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 1205).pointIds 1205)]
theorem treeEq3683 : B3683.tree = HexagonCover.NBand.M6667_6700.SplitData.node3683 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3684
  · rfl
  · rfl

def B2989 : Block := .branch 67 ![1152921504606847361, 1538, 55340233320640288772, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 73).pointIds 73), Tip2986_2990, (.leaf 2 (Common.fact 74).pointIds 74), (.leaf 3 (Common.fact 75).pointIds 75), (.leaf 4 (Common.fact 76).pointIds 76), (.leaf 5 (Common.fact 77).pointIds 77), B3683]
theorem treeEq2989 : B2989.tree = HexagonCover.NBand.M6667_6700.SplitData.node2989 := by
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
  · exact treeEq3683

def B3693 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1216).pointIds 1216)]
theorem treeEq3693 : B3693.tree = HexagonCover.NBand.M6667_6700.SplitData.node3693 := by
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

def B3692 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3693, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1215).pointIds 1215)]
theorem treeEq3692 : B3692.tree = HexagonCover.NBand.M6667_6700.SplitData.node3692 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3693
  · rfl
  · rfl

def B3691 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 5986310706507378354261318027389810221183143480131648] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3692, (.leaf 6 (Common.fact 1214).pointIds 1214)]
theorem treeEq3691 : B3691.tree = HexagonCover.NBand.M6667_6700.SplitData.node3691 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3692
  · rfl

def B2988 : Block := .branch 65 ![1152921504606847361, 1538, 18446745173221185540, 9671406556917033397673992, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 68).pointIds 68), (.leaf 1 (Common.fact 69).pointIds 69), B2989, (.leaf 3 (Common.fact 70).pointIds 70), (.leaf 4 (Common.fact 71).pointIds 71), (.leaf 5 (Common.fact 72).pointIds 72), B3691]
theorem treeEq2988 : B2988.tree = HexagonCover.NBand.M6667_6700.SplitData.node2988 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2989
  · rfl
  · rfl
  · rfl
  · exact treeEq3691

def B2987 : Block := .branch 83 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 97).pointIds 97), (.leaf 1 (Common.fact 98).pointIds 98), (.leaf 2 (Common.fact 1256).pointIds 1256), B2988, (.leaf 4 (Common.fact 100).pointIds 100), (.leaf 5 (Common.fact 101).pointIds 101), (.leaf 6 (Common.fact 989).pointIds 989)]
theorem treeEq2987 : B2987.tree = HexagonCover.NBand.M6667_6700.SplitData.node2987 := by
  change Tree.branch (83 : Fin 173) _ = Tree.branch (83 : Fin 173) _
  apply congrArg (Tree.branch (83 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2988
  · rfl
  · rfl
  · rfl

def B3696 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq3696 : B3696.tree = HexagonCover.NBand.M6667_6700.SplitData.node3696 := by
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

def B3695 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3696, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1218).pointIds 1218)]
theorem treeEq3695 : B3695.tree = HexagonCover.NBand.M6667_6700.SplitData.node3695 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3696
  · rfl
  · rfl

def B3694 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 5986310706507378354261318027389791774439069770580032] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3695, (.leaf 6 (Common.fact 1217).pointIds 1217)]
theorem treeEq3694 : B3694.tree = HexagonCover.NBand.M6667_6700.SplitData.node3694 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3695
  · rfl

def B2986 : Block := .branch 64 ![1152921504606847361, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 63).pointIds 63), (.leaf 1 (Common.fact 64).pointIds 64), B2987, (.leaf 3 (Common.fact 65).pointIds 65), (.leaf 4 (Common.fact 66).pointIds 66), (.leaf 5 (Common.fact 67).pointIds 67), B3694]
theorem treeEq2986 : B2986.tree = HexagonCover.NBand.M6667_6700.SplitData.node2986 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2987
  · rfl
  · rfl
  · rfl
  · exact treeEq3694

theorem accepted2986 : B2986.accepted = true := by decide +kernel
theorem checked2986 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2986 (maskNeeds ![1152921504606847361, 1538, 1099511633924, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2986]
  exact B2986.sound accepted2986
#print axioms checked2986

def B3729 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892639848706894752012860165384044608] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1313).pointIds 1313)]
theorem treeEq3729 : B3729.tree = HexagonCover.NBand.M6667_6700.SplitData.node3729 := by
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

def B3728 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598519562072544015106796327922040896] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3729]
theorem treeEq3728 : B3728.tree = HexagonCover.NBand.M6667_6700.SplitData.node3728 := by
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
  · exact treeEq3729

def B3727 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3728, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3727 : B3727.tree = HexagonCover.NBand.M6667_6700.SplitData.node3727 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3728
  · rfl
  · rfl

def B3732 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 730750818665452757176076695109617380725892841536] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1315).pointIds 1315)]
theorem treeEq3732 : B3732.tree = HexagonCover.NBand.M6667_6700.SplitData.node3732 := by
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

def B3731 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131820649242463767151247424] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3732, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3731 : B3731.tree = HexagonCover.NBand.M6667_6700.SplitData.node3731 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3732
  · rfl
  · rfl

def B3730 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131820649242463767151247424] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3731, (.leaf 6 (Common.fact 1314).pointIds 1314)]
theorem treeEq3730 : B3730.tree = HexagonCover.NBand.M6667_6700.SplitData.node3730 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3731
  · rfl

def B3726 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3727, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3730]
theorem treeEq3726 : B3726.tree = HexagonCover.NBand.M6667_6700.SplitData.node3726 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3727
  · rfl
  · rfl
  · exact treeEq3730

def B3735 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374875169975376599817636288386647833543581179052096] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1317).pointIds 1317)]
theorem treeEq3735 : B3735.tree = HexagonCover.NBand.M6667_6700.SplitData.node3735 := by
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

def B3734 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113686761948244329530654784] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3735, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3734 : B3734.tree = HexagonCover.NBand.M6667_6700.SplitData.node3734 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3735
  · rfl
  · rfl

def B3733 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113686761948244329530654784] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3734, (.leaf 6 (Common.fact 1316).pointIds 1316)]
theorem treeEq3733 : B3733.tree = HexagonCover.NBand.M6667_6700.SplitData.node3733 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3734
  · rfl

def B3725 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![B3726, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3733]
theorem treeEq3725 : B3725.tree = HexagonCover.NBand.M6667_6700.SplitData.node3725 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3726
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3733

def B3724 : Block := .branch 95 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3725, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1312).pointIds 1312)]
theorem treeEq3724 : B3724.tree = HexagonCover.NBand.M6667_6700.SplitData.node3724 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3725
  · rfl
  · rfl
  · rfl

theorem accepted3724 : B3724.accepted = true := by decide +kernel
theorem checked3724 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3724 (maskNeeds ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112477836128629700355948608]) := by
  rw [← treeEq3724]
  exact B3724.sound accepted3724
#print axioms checked3724

def B3753 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864553951735076251741192256] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq3753 : B3753.tree = HexagonCover.NBand.M6667_6700.SplitData.node3753 := by
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

def B3752 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230203214829012414279188544] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3753]
theorem treeEq3752 : B3752.tree = HexagonCover.NBand.M6667_6700.SplitData.node3752 := by
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
  · exact treeEq3753

def B3751 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3752, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1305).pointIds 1305)]
theorem treeEq3751 : B3751.tree = HexagonCover.NBand.M6667_6700.SplitData.node3751 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3752
  · rfl
  · rfl

def B3756 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 1298074234354309339596812249989184] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3756 : B3756.tree = HexagonCover.NBand.M6667_6700.SplitData.node3756 := by
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

def B3755 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270131896207106189681474666560] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3756, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3755 : B3755.tree = HexagonCover.NBand.M6667_6700.SplitData.node3755 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3756
  · rfl
  · rfl

def B3754 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270131896207106189681474666560] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3755, (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq3754 : B3754.tree = HexagonCover.NBand.M6667_6700.SplitData.node3754 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3755
  · rfl

def B3750 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3751, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3754]
theorem treeEq3750 : B3750.tree = HexagonCover.NBand.M6667_6700.SplitData.node3750 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3751
  · rfl
  · rfl
  · exact treeEq3754

def B3759 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3759 : B3759.tree = HexagonCover.NBand.M6667_6700.SplitData.node3759 := by
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

def B3758 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3759, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1308).pointIds 1308)]
theorem treeEq3758 : B3758.tree = HexagonCover.NBand.M6667_6700.SplitData.node3758 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3759
  · rfl
  · rfl

def B3757 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374875169975376599818270113460088357066586560397376] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3758, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3757 : B3757.tree = HexagonCover.NBand.M6667_6700.SplitData.node3757 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3758
  · rfl

def B3749 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![B3750, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3757]
theorem treeEq3749 : B3749.tree = HexagonCover.NBand.M6667_6700.SplitData.node3749 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3750
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3757

def B3748 : Block := .branch 95 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3749, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq3748 : B3748.tree = HexagonCover.NBand.M6667_6700.SplitData.node3748 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3749
  · rfl
  · rfl
  · rfl

theorem accepted3748 : B3748.accepted = true := by decide +kernel
theorem checked3748 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3748 (maskNeeds ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374875169975376599818270112553393992355614679367744]) := by
  rw [← treeEq3748]
  exact B3748.sound accepted3748
#print axioms checked3748

end HexagonCover.NBand.M6667_6700.SplitTree.Run0051
