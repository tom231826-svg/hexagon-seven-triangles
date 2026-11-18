import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0043
import HexagonCover.NBand.M6667_6700.SplitTree.Run0045
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0046
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3149_3154 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3154 ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] HexagonCover.NBand.M6667_6700.SplitTree.Run0045.checked3154
def B3328 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq3328 : B3328.tree = HexagonCover.NBand.M6667_6700.SplitData.node3328 := by
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

def B3327 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3328]
theorem treeEq3327 : B3327.tree = HexagonCover.NBand.M6667_6700.SplitData.node3327 := by
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
  · exact treeEq3328

def B3326 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3327, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3326 : B3326.tree = HexagonCover.NBand.M6667_6700.SplitData.node3326 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3327
  · rfl
  · rfl

def B3153 : Block := .branch 85 ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), Tip3149_3154, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B3326]
theorem treeEq3153 : B3153.tree = HexagonCover.NBand.M6667_6700.SplitData.node3153 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3326

def B3152 : Block := .branch 137 ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), B3153, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq3152 : B3152.tree = HexagonCover.NBand.M6667_6700.SplitData.node3152 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3153
  · rfl
  · rfl

def B3151 : Block := .branch 138 ![1152921504606847361, 1538, 2398076730681753344004, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 646).pointIds 646), B3152, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq3151 : B3151.tree = HexagonCover.NBand.M6667_6700.SplitData.node3151 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3152
  · rfl
  · rfl

def B3331 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3331 : B3331.tree = HexagonCover.NBand.M6667_6700.SplitData.node3331 := by
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

def B3330 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3331, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3330 : B3330.tree = HexagonCover.NBand.M6667_6700.SplitData.node3330 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3331
  · rfl
  · rfl

def B3329 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3330, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3329 : B3329.tree = HexagonCover.NBand.M6667_6700.SplitData.node3329 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3330
  · rfl

def B3150 : Block := .branch 84 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3151, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3329]
theorem treeEq3150 : B3150.tree = HexagonCover.NBand.M6667_6700.SplitData.node3150 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3151
  · rfl
  · rfl
  · exact treeEq3329

def B3334 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3334 : B3334.tree = HexagonCover.NBand.M6667_6700.SplitData.node3334 := by
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

def B3333 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3334, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3333 : B3333.tree = HexagonCover.NBand.M6667_6700.SplitData.node3333 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3334
  · rfl
  · rfl

def B3332 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3333, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3332 : B3332.tree = HexagonCover.NBand.M6667_6700.SplitData.node3332 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3333
  · rfl

def B3149 : Block := .branch 80 ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![B3150, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3332]
theorem treeEq3149 : B3149.tree = HexagonCover.NBand.M6667_6700.SplitData.node3149 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3332

theorem accepted3149 : B3149.accepted = true := by decide +kernel
theorem checked3149 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3149 (maskNeeds ![1152921504606847361, 1538, 2416523474755462895620, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464]) := by
  rw [← treeEq3149]
  exact B3149.sound accepted3149
#print axioms checked3149

def Tip2992_2993 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2993 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0043.checked2993
def B3141 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864478393871350337417773120] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 871).pointIds 871)]
theorem treeEq3141 : B3141.tree = HexagonCover.NBand.M6667_6700.SplitData.node3141 := by
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

def B3140 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230127656965286499955769408] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3141]
theorem treeEq3140 : B3140.tree = HexagonCover.NBand.M6667_6700.SplitData.node3140 := by
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
  · exact treeEq3141

def B3139 : Block := .branch 171 ![385, 1538, 1099511633924, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 763).pointIds 763), B3140, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq3139 : B3139.tree = HexagonCover.NBand.M6667_6700.SplitData.node3139 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3140
  · rfl
  · rfl

def B3144 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq3144 : B3144.tree = HexagonCover.NBand.M6667_6700.SplitData.node3144 := by
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

def B3143 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3144, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 879).pointIds 879)]
theorem treeEq3143 : B3143.tree = HexagonCover.NBand.M6667_6700.SplitData.node3143 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3144
  · rfl
  · rfl

def B3142 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3143, (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq3142 : B3142.tree = HexagonCover.NBand.M6667_6700.SplitData.node3142 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3143
  · rfl

def B3138 : Block := .branch 84 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3139, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3142]
theorem treeEq3138 : B3138.tree = HexagonCover.NBand.M6667_6700.SplitData.node3138 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3139
  · rfl
  · rfl
  · exact treeEq3142

def B3147 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq3147 : B3147.tree = HexagonCover.NBand.M6667_6700.SplitData.node3147 := by
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

def B3146 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3147, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq3146 : B3146.tree = HexagonCover.NBand.M6667_6700.SplitData.node3146 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3147
  · rfl
  · rfl

def B3145 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3146, (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq3145 : B3145.tree = HexagonCover.NBand.M6667_6700.SplitData.node3145 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3146
  · rfl

def B3137 : Block := .branch 80 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![B3138, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3145]
theorem treeEq3137 : B3137.tree = HexagonCover.NBand.M6667_6700.SplitData.node3137 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3138
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3145

def B3136 : Block := .branch 95 ![385, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3137, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1050).pointIds 1050)]
theorem treeEq3136 : B3136.tree = HexagonCover.NBand.M6667_6700.SplitData.node3136 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3137
  · rfl
  · rfl
  · rfl

def B2992 : Block := .branch 78 ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 87).pointIds 87), Tip2992_2993, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B3136]
theorem treeEq2992 : B2992.tree = HexagonCover.NBand.M6667_6700.SplitData.node2992 := by
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
  · exact treeEq3136

theorem accepted2992 : B2992.accepted = true := by decide +kernel
theorem checked2992 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2992 (maskNeeds ![1152921504606847361, 1538, 18446745173221185540, 24584, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2992]
  exact B2992.sound accepted2992
#print axioms checked2992

def B3391 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3391 : B3391.tree = HexagonCover.NBand.M6667_6700.SplitData.node3391 := by
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

def B3390 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3391]
theorem treeEq3390 : B3390.tree = HexagonCover.NBand.M6667_6700.SplitData.node3390 := by
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
  · exact treeEq3391

def B3393 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq3393 : B3393.tree = HexagonCover.NBand.M6667_6700.SplitData.node3393 := by
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

def B3392 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3393, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3392 : B3392.tree = HexagonCover.NBand.M6667_6700.SplitData.node3392 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3393
  · rfl
  · rfl

def B3389 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3390, (.leaf 5 (Common.fact 439).pointIds 439), B3392]
theorem treeEq3389 : B3389.tree = HexagonCover.NBand.M6667_6700.SplitData.node3389 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3390
  · rfl
  · exact treeEq3392

def B3395 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3395 : B3395.tree = HexagonCover.NBand.M6667_6700.SplitData.node3395 := by
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

def B3394 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3395]
theorem treeEq3394 : B3394.tree = HexagonCover.NBand.M6667_6700.SplitData.node3394 := by
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
  · exact treeEq3395

def B3388 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3389, B3394, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3388 : B3388.tree = HexagonCover.NBand.M6667_6700.SplitData.node3388 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3389
  · exact treeEq3394
  · rfl
  · rfl

def B3398 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3398 : B3398.tree = HexagonCover.NBand.M6667_6700.SplitData.node3398 := by
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

def B3397 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3398]
theorem treeEq3397 : B3397.tree = HexagonCover.NBand.M6667_6700.SplitData.node3397 := by
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
  · exact treeEq3398

def B3396 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3397, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3396 : B3396.tree = HexagonCover.NBand.M6667_6700.SplitData.node3396 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3397
  · rfl
  · rfl

def B3387 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3388, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3396, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3387 : B3387.tree = HexagonCover.NBand.M6667_6700.SplitData.node3387 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3388
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3396
  · rfl

def B3401 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3401 : B3401.tree = HexagonCover.NBand.M6667_6700.SplitData.node3401 := by
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

def B3400 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3401]
theorem treeEq3400 : B3400.tree = HexagonCover.NBand.M6667_6700.SplitData.node3400 := by
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
  · exact treeEq3401

def B3399 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3400, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3399 : B3399.tree = HexagonCover.NBand.M6667_6700.SplitData.node3399 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3400
  · rfl
  · rfl

def B3386 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3387, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3399]
theorem treeEq3386 : B3386.tree = HexagonCover.NBand.M6667_6700.SplitData.node3386 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3387
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3399

theorem accepted3386 : B3386.accepted = true := by decide +kernel
theorem checked3386 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3386 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624]) := by
  rw [← treeEq3386]
  exact B3386.sound accepted3386
#print axioms checked3386

def Tip3385_3386 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3386 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] checked3386
def B3407 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3407 : B3407.tree = HexagonCover.NBand.M6667_6700.SplitData.node3407 := by
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

def B3406 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3407]
theorem treeEq3406 : B3406.tree = HexagonCover.NBand.M6667_6700.SplitData.node3406 := by
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
  · exact treeEq3407

def B3409 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq3409 : B3409.tree = HexagonCover.NBand.M6667_6700.SplitData.node3409 := by
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

def B3408 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3409, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3408 : B3408.tree = HexagonCover.NBand.M6667_6700.SplitData.node3408 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3409
  · rfl
  · rfl

def B3405 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3406, (.leaf 5 (Common.fact 439).pointIds 439), B3408]
theorem treeEq3405 : B3405.tree = HexagonCover.NBand.M6667_6700.SplitData.node3405 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3406
  · rfl
  · exact treeEq3408

def B3411 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq3411 : B3411.tree = HexagonCover.NBand.M6667_6700.SplitData.node3411 := by
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

def B3410 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3411]
theorem treeEq3410 : B3410.tree = HexagonCover.NBand.M6667_6700.SplitData.node3410 := by
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
  · exact treeEq3411

def B3404 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3405, B3410, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3404 : B3404.tree = HexagonCover.NBand.M6667_6700.SplitData.node3404 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3405
  · exact treeEq3410
  · rfl
  · rfl

def B3414 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq3414 : B3414.tree = HexagonCover.NBand.M6667_6700.SplitData.node3414 := by
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

def B3413 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3414]
theorem treeEq3413 : B3413.tree = HexagonCover.NBand.M6667_6700.SplitData.node3413 := by
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
  · exact treeEq3414

def B3412 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3413, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3412 : B3412.tree = HexagonCover.NBand.M6667_6700.SplitData.node3412 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3413
  · rfl
  · rfl

def B3403 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3404, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3412, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3403 : B3403.tree = HexagonCover.NBand.M6667_6700.SplitData.node3403 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3404
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3412
  · rfl

def B3417 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3417 : B3417.tree = HexagonCover.NBand.M6667_6700.SplitData.node3417 := by
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

def B3416 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3417]
theorem treeEq3416 : B3416.tree = HexagonCover.NBand.M6667_6700.SplitData.node3416 := by
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
  · exact treeEq3417

def B3415 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3416, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3415 : B3415.tree = HexagonCover.NBand.M6667_6700.SplitData.node3415 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3416
  · rfl
  · rfl

def B3402 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B3403, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3415]
theorem treeEq3402 : B3402.tree = HexagonCover.NBand.M6667_6700.SplitData.node3402 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3403
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3415

def B3385 : Block := .branch 74 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip3385_3386, B3402, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1024).pointIds 1024)]
theorem treeEq3385 : B3385.tree = HexagonCover.NBand.M6667_6700.SplitData.node3385 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3402
  · rfl
  · rfl
  · rfl

theorem accepted3385 : B3385.accepted = true := by decide +kernel
theorem checked3385 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3385 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776]) := by
  rw [← treeEq3385]
  exact B3385.sound accepted3385
#print axioms checked3385

def B3433 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3433 : B3433.tree = HexagonCover.NBand.M6667_6700.SplitData.node3433 := by
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

def B3432 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B3433]
theorem treeEq3432 : B3432.tree = HexagonCover.NBand.M6667_6700.SplitData.node3432 := by
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
  · exact treeEq3433

def B3435 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq3435 : B3435.tree = HexagonCover.NBand.M6667_6700.SplitData.node3435 := by
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

def B3434 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3435, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3434 : B3434.tree = HexagonCover.NBand.M6667_6700.SplitData.node3434 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3435
  · rfl
  · rfl

def B3431 : Block := .branch 128 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B3432, (.leaf 5 (Common.fact 439).pointIds 439), B3434]
theorem treeEq3431 : B3431.tree = HexagonCover.NBand.M6667_6700.SplitData.node3431 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3432
  · rfl
  · exact treeEq3434

def B3437 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq3437 : B3437.tree = HexagonCover.NBand.M6667_6700.SplitData.node3437 := by
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

def B3436 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B3437]
theorem treeEq3436 : B3436.tree = HexagonCover.NBand.M6667_6700.SplitData.node3436 := by
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
  · exact treeEq3437

def B3430 : Block := .branch 127 ![385, 1538, 1099511633924, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376686569847858686053580864] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B3431, B3436, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq3430 : B3430.tree = HexagonCover.NBand.M6667_6700.SplitData.node3430 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3431
  · exact treeEq3436
  · rfl
  · rfl

def B3440 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq3440 : B3440.tree = HexagonCover.NBand.M6667_6700.SplitData.node3440 := by
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

def B3439 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B3440]
theorem treeEq3439 : B3439.tree = HexagonCover.NBand.M6667_6700.SplitData.node3439 := by
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
  · exact treeEq3440

def B3438 : Block := .branch 167 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818557646125237003065387937758183488] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3439, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq3438 : B3438.tree = HexagonCover.NBand.M6667_6700.SplitData.node3438 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3439
  · rfl
  · rfl

def B3429 : Block := .branch 125 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3430, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B3438, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq3429 : B3429.tree = HexagonCover.NBand.M6667_6700.SplitData.node3429 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3430
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3438
  · rfl

def B3443 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq3443 : B3443.tree = HexagonCover.NBand.M6667_6700.SplitData.node3443 := by
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

def B3442 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3443]
theorem treeEq3442 : B3442.tree = HexagonCover.NBand.M6667_6700.SplitData.node3442 := by
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
  · exact treeEq3443

def B3441 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3442, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq3441 : B3441.tree = HexagonCover.NBand.M6667_6700.SplitData.node3441 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3442
  · rfl
  · rfl

def B3428 : Block := .branch 123 ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B3429, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3441]
theorem treeEq3428 : B3428.tree = HexagonCover.NBand.M6667_6700.SplitData.node3428 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3429
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3441

theorem accepted3428 : B3428.accepted = true := by decide +kernel
theorem checked3428 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3428 (maskNeeds ![385, 1538, 1099511633924, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120]) := by
  rw [← treeEq3428]
  exact B3428.sound accepted3428
#print axioms checked3428

end HexagonCover.NBand.M6667_6700.SplitTree.Run0046
