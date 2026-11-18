import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0016
import HexagonCover.NBand.M6667_6700.SplitTree.Run0017
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0018
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1225_1260 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1260 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] HexagonCover.NBand.M6667_6700.SplitTree.Run0016.checked1260
def Tip1225_1226 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1226 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] HexagonCover.NBand.M6667_6700.SplitTree.Run0017.checked1226
def B1281 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1281 : B1281.tree = HexagonCover.NBand.M6667_6700.SplitData.node1281 := by
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

def B1280 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1281]
theorem treeEq1280 : B1280.tree = HexagonCover.NBand.M6667_6700.SplitData.node1280 := by
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
  · exact treeEq1281

def B1283 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq1283 : B1283.tree = HexagonCover.NBand.M6667_6700.SplitData.node1283 := by
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

def B1282 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1283, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1282 : B1282.tree = HexagonCover.NBand.M6667_6700.SplitData.node1282 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1283
  · rfl
  · rfl

def B1279 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1280, (.leaf 5 (Common.fact 439).pointIds 439), B1282]
theorem treeEq1279 : B1279.tree = HexagonCover.NBand.M6667_6700.SplitData.node1279 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1280
  · rfl
  · exact treeEq1282

def B1285 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq1285 : B1285.tree = HexagonCover.NBand.M6667_6700.SplitData.node1285 := by
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

def B1284 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1285]
theorem treeEq1284 : B1284.tree = HexagonCover.NBand.M6667_6700.SplitData.node1284 := by
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
  · exact treeEq1285

def B1278 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1279, B1284, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1278 : B1278.tree = HexagonCover.NBand.M6667_6700.SplitData.node1278 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1279
  · exact treeEq1284
  · rfl
  · rfl

def B1288 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq1288 : B1288.tree = HexagonCover.NBand.M6667_6700.SplitData.node1288 := by
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

def B1287 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1288]
theorem treeEq1287 : B1287.tree = HexagonCover.NBand.M6667_6700.SplitData.node1287 := by
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
  · exact treeEq1288

def B1286 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1287, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1286 : B1286.tree = HexagonCover.NBand.M6667_6700.SplitData.node1286 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1287
  · rfl
  · rfl

def B1277 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1278, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1286, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1277 : B1277.tree = HexagonCover.NBand.M6667_6700.SplitData.node1277 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1278
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1286
  · rfl

def B1291 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1291 : B1291.tree = HexagonCover.NBand.M6667_6700.SplitData.node1291 := by
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

def B1290 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1291]
theorem treeEq1290 : B1290.tree = HexagonCover.NBand.M6667_6700.SplitData.node1290 := by
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
  · exact treeEq1291

def B1289 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1290, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1289 : B1289.tree = HexagonCover.NBand.M6667_6700.SplitData.node1289 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1290
  · rfl
  · rfl

def B1276 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B1277, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1289]
theorem treeEq1276 : B1276.tree = HexagonCover.NBand.M6667_6700.SplitData.node1276 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1277
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1289

def B1259 : Block := .branch 74 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip1225_1260, B1276, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq1259 : B1259.tree = HexagonCover.NBand.M6667_6700.SplitData.node1259 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1276
  · rfl
  · rfl
  · rfl

def B1225 : Block := .branch 73 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip1225_1226, B1259, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M6667_6700.SplitData.node1225 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1259
  · rfl
  · rfl
  · rfl

theorem accepted1225 : B1225.accepted = true := by decide +kernel
theorem checked1225 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1225 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656]) := by
  rw [← treeEq1225]
  exact B1225.sound accepted1225
#print axioms checked1225

def B1367 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1367 : B1367.tree = HexagonCover.NBand.M6667_6700.SplitData.node1367 := by
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

def B1366 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1367]
theorem treeEq1366 : B1366.tree = HexagonCover.NBand.M6667_6700.SplitData.node1366 := by
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
  · exact treeEq1367

def B1369 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq1369 : B1369.tree = HexagonCover.NBand.M6667_6700.SplitData.node1369 := by
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

def B1368 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1369, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1368 : B1368.tree = HexagonCover.NBand.M6667_6700.SplitData.node1368 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1369
  · rfl
  · rfl

def B1365 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1366, (.leaf 5 (Common.fact 439).pointIds 439), B1368]
theorem treeEq1365 : B1365.tree = HexagonCover.NBand.M6667_6700.SplitData.node1365 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1366
  · rfl
  · exact treeEq1368

def B1371 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1371 : B1371.tree = HexagonCover.NBand.M6667_6700.SplitData.node1371 := by
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

def B1370 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1371]
theorem treeEq1370 : B1370.tree = HexagonCover.NBand.M6667_6700.SplitData.node1370 := by
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
  · exact treeEq1371

def B1364 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1365, B1370, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1364 : B1364.tree = HexagonCover.NBand.M6667_6700.SplitData.node1364 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1365
  · exact treeEq1370
  · rfl
  · rfl

def B1374 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1374 : B1374.tree = HexagonCover.NBand.M6667_6700.SplitData.node1374 := by
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

def B1373 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1374]
theorem treeEq1373 : B1373.tree = HexagonCover.NBand.M6667_6700.SplitData.node1373 := by
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
  · exact treeEq1374

def B1372 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1373, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1372 : B1372.tree = HexagonCover.NBand.M6667_6700.SplitData.node1372 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1373
  · rfl
  · rfl

def B1363 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1364, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1372, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1363 : B1363.tree = HexagonCover.NBand.M6667_6700.SplitData.node1363 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1364
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1372
  · rfl

def B1377 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1377 : B1377.tree = HexagonCover.NBand.M6667_6700.SplitData.node1377 := by
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

def B1376 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1377]
theorem treeEq1376 : B1376.tree = HexagonCover.NBand.M6667_6700.SplitData.node1376 := by
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
  · exact treeEq1377

def B1375 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1376, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1375 : B1375.tree = HexagonCover.NBand.M6667_6700.SplitData.node1375 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1376
  · rfl
  · rfl

def B1362 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1363, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1375]
theorem treeEq1362 : B1362.tree = HexagonCover.NBand.M6667_6700.SplitData.node1362 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1363
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1375

theorem accepted1362 : B1362.accepted = true := by decide +kernel
theorem checked1362 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1362 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000]) := by
  rw [← treeEq1362]
  exact B1362.sound accepted1362
#print axioms checked1362

def B1400 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1400 : B1400.tree = HexagonCover.NBand.M6667_6700.SplitData.node1400 := by
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

def B1399 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1400]
theorem treeEq1399 : B1399.tree = HexagonCover.NBand.M6667_6700.SplitData.node1399 := by
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
  · exact treeEq1400

def B1402 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq1402 : B1402.tree = HexagonCover.NBand.M6667_6700.SplitData.node1402 := by
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

def B1401 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1402, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1401 : B1401.tree = HexagonCover.NBand.M6667_6700.SplitData.node1401 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1402
  · rfl
  · rfl

def B1398 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1399, (.leaf 5 (Common.fact 439).pointIds 439), B1401]
theorem treeEq1398 : B1398.tree = HexagonCover.NBand.M6667_6700.SplitData.node1398 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1399
  · rfl
  · exact treeEq1401

def B1404 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1404 : B1404.tree = HexagonCover.NBand.M6667_6700.SplitData.node1404 := by
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

def B1403 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1404]
theorem treeEq1403 : B1403.tree = HexagonCover.NBand.M6667_6700.SplitData.node1403 := by
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
  · exact treeEq1404

def B1397 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1398, B1403, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1397 : B1397.tree = HexagonCover.NBand.M6667_6700.SplitData.node1397 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1398
  · exact treeEq1403
  · rfl
  · rfl

def B1407 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1407 : B1407.tree = HexagonCover.NBand.M6667_6700.SplitData.node1407 := by
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

def B1406 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1407]
theorem treeEq1406 : B1406.tree = HexagonCover.NBand.M6667_6700.SplitData.node1406 := by
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
  · exact treeEq1407

def B1405 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1406, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1405 : B1405.tree = HexagonCover.NBand.M6667_6700.SplitData.node1405 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1406
  · rfl
  · rfl

def B1396 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1397, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1405, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1396 : B1396.tree = HexagonCover.NBand.M6667_6700.SplitData.node1396 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1397
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1405
  · rfl

def B1410 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1410 : B1410.tree = HexagonCover.NBand.M6667_6700.SplitData.node1410 := by
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

def B1409 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1410]
theorem treeEq1409 : B1409.tree = HexagonCover.NBand.M6667_6700.SplitData.node1409 := by
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
  · exact treeEq1410

def B1408 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1409, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1408 : B1408.tree = HexagonCover.NBand.M6667_6700.SplitData.node1408 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1409
  · rfl
  · rfl

def B1395 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1396, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1408]
theorem treeEq1395 : B1395.tree = HexagonCover.NBand.M6667_6700.SplitData.node1395 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1396
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1408

theorem accepted1395 : B1395.accepted = true := by decide +kernel
theorem checked1395 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1395 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000]) := by
  rw [← treeEq1395]
  exact B1395.sound accepted1395
#print axioms checked1395

def Tip1361_1362 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1362 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] checked1362
def B1383 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1383 : B1383.tree = HexagonCover.NBand.M6667_6700.SplitData.node1383 := by
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

def B1382 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1383]
theorem treeEq1382 : B1382.tree = HexagonCover.NBand.M6667_6700.SplitData.node1382 := by
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
  · exact treeEq1383

def B1385 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 943).pointIds 943)]
theorem treeEq1385 : B1385.tree = HexagonCover.NBand.M6667_6700.SplitData.node1385 := by
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

def B1384 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295483890669805503746932800] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1385, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1384 : B1384.tree = HexagonCover.NBand.M6667_6700.SplitData.node1384 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1385
  · rfl
  · rfl

def B1381 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1382, (.leaf 5 (Common.fact 439).pointIds 439), B1384]
theorem treeEq1381 : B1381.tree = HexagonCover.NBand.M6667_6700.SplitData.node1381 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1382
  · rfl
  · exact treeEq1384

def B1387 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883829100653165439580897344] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 941).pointIds 941)]
theorem treeEq1387 : B1387.tree = HexagonCover.NBand.M6667_6700.SplitData.node1387 := by
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

def B1386 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249478363747101602118893632] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1387]
theorem treeEq1386 : B1386.tree = HexagonCover.NBand.M6667_6700.SplitData.node1386 := by
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
  · exact treeEq1387

def B1380 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376762127711584600377000000] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1381, B1386, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1380 : B1380.tree = HexagonCover.NBand.M6667_6700.SplitData.node1380 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1381
  · exact treeEq1386
  · rfl
  · rfl

def B1390 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894423374919453421826736192] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 942).pointIds 942)]
theorem treeEq1390 : B1390.tree = HexagonCover.NBand.M6667_6700.SplitData.node1390 := by
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

def B1389 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053357020427295198071978721344] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1390]
theorem treeEq1389 : B1389.tree = HexagonCover.NBand.M6667_6700.SplitData.node1389 := by
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
  · exact treeEq1390

def B1388 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818233444484304191259681070236827712] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1389, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq1388 : B1388.tree = HexagonCover.NBand.M6667_6700.SplitData.node1388 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1389
  · rfl
  · rfl

def B1379 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1380, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1388, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1379 : B1379.tree = HexagonCover.NBand.M6667_6700.SplitData.node1379 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1380
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1388
  · rfl

def B1393 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq1393 : B1393.tree = HexagonCover.NBand.M6667_6700.SplitData.node1393 := by
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

def B1392 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1393]
theorem treeEq1392 : B1392.tree = HexagonCover.NBand.M6667_6700.SplitData.node1392 := by
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
  · exact treeEq1393

def B1391 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1392, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq1391 : B1391.tree = HexagonCover.NBand.M6667_6700.SplitData.node1391 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1392
  · rfl
  · rfl

def B1378 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095482847442376762127711584600377000000] ![B1379, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1391]
theorem treeEq1378 : B1378.tree = HexagonCover.NBand.M6667_6700.SplitData.node1378 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1379
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1391

def B1361 : Block := .branch 74 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip1361_1362, B1378, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq1361 : B1361.tree = HexagonCover.NBand.M6667_6700.SplitData.node1361 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1378
  · rfl
  · rfl
  · rfl

theorem accepted1361 : B1361.accepted = true := by decide +kernel
theorem checked1361 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1361 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141303433946593873519198720937689152]) := by
  rw [← treeEq1361]
  exact B1361.sound accepted1361
#print axioms checked1361

end HexagonCover.NBand.M6667_6700.SplitTree.Run0018
