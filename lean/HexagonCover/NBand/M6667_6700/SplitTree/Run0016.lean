import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0015
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0913_0918 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0918 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] HexagonCover.NBand.M6667_6700.SplitTree.Run0015.checked0918
def B1165 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M6667_6700.SplitData.node1165 := by
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

def B1164 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511795441116629495843142850553700679744] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), (.leaf 4 (Common.fact 737).pointIds 737), B1165, (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M6667_6700.SplitData.node1164 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1165
  · rfl

def B1163 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1164]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M6667_6700.SplitData.node1163 := by
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
  · exact treeEq1164

def B1162 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1163, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M6667_6700.SplitData.node1162 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1163
  · rfl
  · rfl

def B0917 : Block := .branch 91 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![Tip0913_0918, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B1162]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M6667_6700.SplitData.node0917 := by
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
  · exact treeEq1162

def B1169 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq1169 : B1169.tree = HexagonCover.NBand.M6667_6700.SplitData.node1169 := by
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

def B1168 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1169, (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M6667_6700.SplitData.node1168 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1169
  · rfl

def B1167 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923601340401583679807684672] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1168]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M6667_6700.SplitData.node1167 := by
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
  · exact treeEq1168

def B1166 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138235047308716303889989696] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1167, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M6667_6700.SplitData.node1166 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1167
  · rfl
  · rfl

def B0916 : Block := .branch 89 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 117).pointIds 117), B0917, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B1166]
theorem treeEq0916 : B0916.tree = HexagonCover.NBand.M6667_6700.SplitData.node0916 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0917
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1166

def B1173 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1173 : B1173.tree = HexagonCover.NBand.M6667_6700.SplitData.node1173 := by
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

def B1172 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1173, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1172 : B1172.tree = HexagonCover.NBand.M6667_6700.SplitData.node1172 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1173
  · rfl

def B1171 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1172]
theorem treeEq1171 : B1171.tree = HexagonCover.NBand.M6667_6700.SplitData.node1171 := by
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
  · exact treeEq1172

def B1170 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1171, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1170 : B1170.tree = HexagonCover.NBand.M6667_6700.SplitData.node1170 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1171
  · rfl
  · rfl

def B0915 : Block := .branch 86 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B0916, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1170]
theorem treeEq0915 : B0915.tree = HexagonCover.NBand.M6667_6700.SplitData.node0915 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0916
  · rfl
  · rfl
  · exact treeEq1170

def B1176 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356890317740949975887586525248] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq1176 : B1176.tree = HexagonCover.NBand.M6667_6700.SplitData.node1176 := by
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

def B1175 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070255967004043912050124521536] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1176]
theorem treeEq1175 : B1175.tree = HexagonCover.NBand.M6667_6700.SplitData.node1175 := by
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
  · exact treeEq1176

def B1174 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321144470600710951044674206826560] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1175, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq1174 : B1174.tree = HexagonCover.NBand.M6667_6700.SplitData.node1174 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1175
  · rfl
  · rfl

def B0914 : Block := .branch 85 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B0915, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B1174]
theorem treeEq0914 : B0914.tree = HexagonCover.NBand.M6667_6700.SplitData.node0914 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0915
  · rfl
  · rfl
  · exact treeEq1174

def B0913 : Block := .branch 137 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), B0914, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq0913 : B0913.tree = HexagonCover.NBand.M6667_6700.SplitData.node0913 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0914
  · rfl
  · rfl

theorem accepted0913 : B0913.accepted = true := by decide +kernel
theorem checked0913 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0913 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq0913]
  exact B0913.sound accepted0913
#print axioms checked0913

def B1190 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864478393871350337417773120] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 871).pointIds 871)]
theorem treeEq1190 : B1190.tree = HexagonCover.NBand.M6667_6700.SplitData.node1190 := by
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

def B1189 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230127656965286499955769408] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1190]
theorem treeEq1189 : B1189.tree = HexagonCover.NBand.M6667_6700.SplitData.node1189 := by
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
  · exact treeEq1190

def B1188 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1189, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq1188 : B1188.tree = HexagonCover.NBand.M6667_6700.SplitData.node1188 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1189
  · rfl
  · rfl

def B1193 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq1193 : B1193.tree = HexagonCover.NBand.M6667_6700.SplitData.node1193 := by
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

def B1192 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1193, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 879).pointIds 879)]
theorem treeEq1192 : B1192.tree = HexagonCover.NBand.M6667_6700.SplitData.node1192 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1193
  · rfl
  · rfl

def B1191 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1192, (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq1191 : B1191.tree = HexagonCover.NBand.M6667_6700.SplitData.node1191 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1192
  · rfl

def B1187 : Block := .branch 84 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B1188, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B1191]
theorem treeEq1187 : B1187.tree = HexagonCover.NBand.M6667_6700.SplitData.node1187 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1188
  · rfl
  · rfl
  · exact treeEq1191

def B1196 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq1196 : B1196.tree = HexagonCover.NBand.M6667_6700.SplitData.node1196 := by
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

def B1195 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1196, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq1195 : B1195.tree = HexagonCover.NBand.M6667_6700.SplitData.node1195 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1196
  · rfl
  · rfl

def B1194 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 98320, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1195, (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq1194 : B1194.tree = HexagonCover.NBand.M6667_6700.SplitData.node1194 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1195
  · rfl

def B1186 : Block := .branch 80 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![B1187, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B1194]
theorem treeEq1186 : B1186.tree = HexagonCover.NBand.M6667_6700.SplitData.node1186 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1187
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1194

def B1185 : Block := .branch 95 ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), B1186, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1050).pointIds 1050)]
theorem treeEq1185 : B1185.tree = HexagonCover.NBand.M6667_6700.SplitData.node1185 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1186
  · rfl
  · rfl
  · rfl

theorem accepted1185 : B1185.accepted = true := by decide +kernel
theorem checked1185 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1185 (maskNeeds ![1152921504606847361, 147573953689188042242, 55340232221128660996, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432]) := by
  rw [← treeEq1185]
  exact B1185.sound accepted1185
#print axioms checked1185

def B1232 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M6667_6700.SplitData.node1232 := by
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

def B1231 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1232]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M6667_6700.SplitData.node1231 := by
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
  · exact treeEq1232

def B1234 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M6667_6700.SplitData.node1234 := by
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

def B1233 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1234, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M6667_6700.SplitData.node1233 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1234
  · rfl
  · rfl

def B1230 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1231, (.leaf 5 (Common.fact 439).pointIds 439), B1233]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M6667_6700.SplitData.node1230 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1231
  · rfl
  · exact treeEq1233

def B1236 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M6667_6700.SplitData.node1236 := by
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

def B1235 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1236]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M6667_6700.SplitData.node1235 := by
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
  · exact treeEq1236

def B1229 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1230, B1235, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M6667_6700.SplitData.node1229 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1230
  · exact treeEq1235
  · rfl
  · rfl

def B1239 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1239 : B1239.tree = HexagonCover.NBand.M6667_6700.SplitData.node1239 := by
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

def B1238 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1239]
theorem treeEq1238 : B1238.tree = HexagonCover.NBand.M6667_6700.SplitData.node1238 := by
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
  · exact treeEq1239

def B1237 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1238, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M6667_6700.SplitData.node1237 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1238
  · rfl
  · rfl

def B1228 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1229, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1237, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M6667_6700.SplitData.node1228 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1229
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1237
  · rfl

def B1242 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1242 : B1242.tree = HexagonCover.NBand.M6667_6700.SplitData.node1242 := by
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

def B1241 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1242]
theorem treeEq1241 : B1241.tree = HexagonCover.NBand.M6667_6700.SplitData.node1241 := by
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
  · exact treeEq1242

def B1240 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1241, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1240 : B1240.tree = HexagonCover.NBand.M6667_6700.SplitData.node1240 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1241
  · rfl
  · rfl

def B1227 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1228, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1240]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M6667_6700.SplitData.node1227 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1228
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1240

theorem accepted1227 : B1227.accepted = true := by decide +kernel
theorem checked1227 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1227 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq1227]
  exact B1227.sound accepted1227
#print axioms checked1227

def B1265 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1265 : B1265.tree = HexagonCover.NBand.M6667_6700.SplitData.node1265 := by
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

def B1264 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1265]
theorem treeEq1264 : B1264.tree = HexagonCover.NBand.M6667_6700.SplitData.node1264 := by
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
  · exact treeEq1265

def B1267 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq1267 : B1267.tree = HexagonCover.NBand.M6667_6700.SplitData.node1267 := by
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

def B1266 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1267, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1266 : B1266.tree = HexagonCover.NBand.M6667_6700.SplitData.node1266 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1267
  · rfl
  · rfl

def B1263 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1264, (.leaf 5 (Common.fact 439).pointIds 439), B1266]
theorem treeEq1263 : B1263.tree = HexagonCover.NBand.M6667_6700.SplitData.node1263 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1264
  · rfl
  · exact treeEq1266

def B1269 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1269 : B1269.tree = HexagonCover.NBand.M6667_6700.SplitData.node1269 := by
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

def B1268 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1269]
theorem treeEq1268 : B1268.tree = HexagonCover.NBand.M6667_6700.SplitData.node1268 := by
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
  · exact treeEq1269

def B1262 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1263, B1268, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1262 : B1262.tree = HexagonCover.NBand.M6667_6700.SplitData.node1262 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1263
  · exact treeEq1268
  · rfl
  · rfl

def B1272 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1272 : B1272.tree = HexagonCover.NBand.M6667_6700.SplitData.node1272 := by
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

def B1271 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1272]
theorem treeEq1271 : B1271.tree = HexagonCover.NBand.M6667_6700.SplitData.node1271 := by
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
  · exact treeEq1272

def B1270 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1271, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1270 : B1270.tree = HexagonCover.NBand.M6667_6700.SplitData.node1270 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1271
  · rfl
  · rfl

def B1261 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1262, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1270, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1261 : B1261.tree = HexagonCover.NBand.M6667_6700.SplitData.node1261 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1262
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1270
  · rfl

def B1275 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1275 : B1275.tree = HexagonCover.NBand.M6667_6700.SplitData.node1275 := by
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

def B1274 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1275]
theorem treeEq1274 : B1274.tree = HexagonCover.NBand.M6667_6700.SplitData.node1274 := by
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
  · exact treeEq1275

def B1273 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1274, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1273 : B1273.tree = HexagonCover.NBand.M6667_6700.SplitData.node1273 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1274
  · rfl
  · rfl

def B1260 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1261, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1273]
theorem treeEq1260 : B1260.tree = HexagonCover.NBand.M6667_6700.SplitData.node1260 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1261
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1273

theorem accepted1260 : B1260.accepted = true := by decide +kernel
theorem checked1260 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1260 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq1260]
  exact B1260.sound accepted1260
#print axioms checked1260

end HexagonCover.NBand.M6667_6700.SplitTree.Run0016
