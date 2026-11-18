import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0016
import HexagonCover.NBand.M8500_8700.SplitTree.Run0017
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0018
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip1075_1079 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1079 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0016.checked1079
def Tip1075_1208 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1208 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0017.checked1208
def B1206 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1206 : B1206.tree = HexagonCover.NBand.M8500_8700.SplitData.node1206 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1205 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1206, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq1205 : B1205.tree = HexagonCover.NBand.M8500_8700.SplitData.node1205 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1206
  · rfl
  · rfl
  · rfl

def B1204 : Block := .branch 160 ![1237940335011998006369059201, 928606182084975731996100098, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B1205]
theorem treeEq1204 : B1204.tree = HexagonCover.NBand.M8500_8700.SplitData.node1204 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1205

def B1078 : Block := .branch 89 ![1237940335011998006369059201, 309636162442285594546537986, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip1075_1079, B1204, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M8500_8700.SplitData.node1078 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1204
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1335 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1335 : B1335.tree = HexagonCover.NBand.M8500_8700.SplitData.node1335 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1334 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1335, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq1334 : B1334.tree = HexagonCover.NBand.M8500_8700.SplitData.node1334 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1335
  · rfl
  · rfl
  · rfl

def B1333 : Block := .branch 160 ![1237940335011998006369059201, 619121172263630663271319042, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 897).pointIds 897), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B1334]
theorem treeEq1333 : B1333.tree = HexagonCover.NBand.M8500_8700.SplitData.node1333 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1334

def B1207 : Block := .branch 89 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![Tip1075_1208, B1333, (.leaf 2 (Common.fact 270).pointIds 270), (.leaf 3 (Common.fact 271).pointIds 271), (.leaf 4 (Common.fact 272).pointIds 272), (.leaf 5 (Common.fact 273).pointIds 273), (.leaf 6 (Common.fact 274).pointIds 274)]
theorem treeEq1207 : B1207.tree = HexagonCover.NBand.M8500_8700.SplitData.node1207 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1333
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1077 : Block := .branch 88 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 265).pointIds 265), B1078, B1207, (.leaf 3 (Common.fact 266).pointIds 266), (.leaf 4 (Common.fact 267).pointIds 267), (.leaf 5 (Common.fact 268).pointIds 268), (.leaf 6 (Common.fact 269).pointIds 269)]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M8500_8700.SplitData.node1077 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1078
  · exact treeEq1207
  · rfl
  · rfl
  · rfl
  · rfl

def B1338 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1338 : B1338.tree = HexagonCover.NBand.M8500_8700.SplitData.node1338 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1337 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1338, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1337 : B1337.tree = HexagonCover.NBand.M8500_8700.SplitData.node1337 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1338
  · rfl

def B1336 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158533696280984011454269120520, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1337]
theorem treeEq1336 : B1336.tree = HexagonCover.NBand.M8500_8700.SplitData.node1336 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1337

def B1076 : Block := .branch 86 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), B1077, B1336, (.leaf 4 (Common.fact 262).pointIds 262), (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M8500_8700.SplitData.node1076 := by
  change Tree.branch (86 : Fin 175) _ = Tree.branch (86 : Fin 175) _
  apply congrArg (Tree.branch (86 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1077
  · exact treeEq1336
  · rfl
  · rfl
  · rfl

def B1341 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1341 : B1341.tree = HexagonCover.NBand.M8500_8700.SplitData.node1341 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1340 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1341, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1340 : B1340.tree = HexagonCover.NBand.M8500_8700.SplitData.node1340 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1341
  · rfl

def B1339 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158495010654756343320678522888, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 882).pointIds 882), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1340]
theorem treeEq1339 : B1339.tree = HexagonCover.NBand.M8500_8700.SplitData.node1339 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1340

def B1075 : Block := .branch 85 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), B1076, B1339, (.leaf 4 (Common.fact 257).pointIds 257), (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq1075 : B1075.tree = HexagonCover.NBand.M8500_8700.SplitData.node1075 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1076
  · exact treeEq1339
  · rfl
  · rfl
  · rfl

theorem accepted1075 : B1075.accepted = true := by decide +kernel
theorem checked1075 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1075 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq1075]
  exact B1075.sound accepted1075
#print axioms checked1075

def Tip1071_1075 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node1075 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] checked1075
def B1344 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1344 : B1344.tree = HexagonCover.NBand.M8500_8700.SplitData.node1344 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1343 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1344, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1343 : B1343.tree = HexagonCover.NBand.M8500_8700.SplitData.node1343 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1344
  · rfl

def B1342 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1343]
theorem treeEq1342 : B1342.tree = HexagonCover.NBand.M8500_8700.SplitData.node1342 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1343

def B1074 : Block := .branch 84 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip1071_1075, B1342, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq1074 : B1074.tree = HexagonCover.NBand.M8500_8700.SplitData.node1074 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1342
  · rfl
  · rfl
  · rfl

def B1347 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq1347 : B1347.tree = HexagonCover.NBand.M8500_8700.SplitData.node1347 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1346 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1347, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq1346 : B1346.tree = HexagonCover.NBand.M8500_8700.SplitData.node1346 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1347
  · rfl

def B1345 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1346]
theorem treeEq1345 : B1345.tree = HexagonCover.NBand.M8500_8700.SplitData.node1345 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1346

def B1073 : Block := .branch 83 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B1074, B1345, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq1073 : B1073.tree = HexagonCover.NBand.M8500_8700.SplitData.node1073 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1074
  · exact treeEq1345
  · rfl
  · rfl
  · rfl

def B1352 : Block := .branch 170 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq1352 : B1352.tree = HexagonCover.NBand.M8500_8700.SplitData.node1352 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1351 : Block := .branch 169 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 894).pointIds 894), (.leaf 2 (Common.fact 895).pointIds 895), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), B1352, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq1351 : B1351.tree = HexagonCover.NBand.M8500_8700.SplitData.node1351 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1352
  · rfl

def B1350 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1351]
theorem treeEq1350 : B1350.tree = HexagonCover.NBand.M8500_8700.SplitData.node1350 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1351

def B1349 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1350, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq1349 : B1349.tree = HexagonCover.NBand.M8500_8700.SplitData.node1349 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1350
  · rfl
  · rfl
  · rfl

def B1348 : Block := .branch 161 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 898).pointIds 898), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B1349]
theorem treeEq1348 : B1348.tree = HexagonCover.NBand.M8500_8700.SplitData.node1348 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1349

def B1072 : Block := .branch 82 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B1073, B1348, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq1072 : B1072.tree = HexagonCover.NBand.M8500_8700.SplitData.node1072 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1073
  · exact treeEq1348
  · rfl
  · rfl
  · rfl

def B1355 : Block := .branch 171 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 891).pointIds 891), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1355 : B1355.tree = HexagonCover.NBand.M8500_8700.SplitData.node1355 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1354 : Block := .branch 172 ![1237940335011998006369059201, 151152620940525821756930, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 866).pointIds 866), (.leaf 1 (Common.fact 888).pointIds 888), (.leaf 2 (Common.fact 889).pointIds 889), B1355, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq1354 : B1354.tree = HexagonCover.NBand.M8500_8700.SplitData.node1354 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1355
  · rfl
  · rfl
  · rfl

def B1353 : Block := .branch 160 ![1237940335011998006369059201, 453384075844183115433474, 75557863725914323425284, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 899).pointIds 899), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B1354]
theorem treeEq1353 : B1353.tree = HexagonCover.NBand.M8500_8700.SplitData.node1353 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1354

def B1071 : Block := .branch 78 ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B1072, B1353, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq1071 : B1071.tree = HexagonCover.NBand.M8500_8700.SplitData.node1071 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1072
  · exact treeEq1353
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1071 : B1071.accepted = true := by decide +kernel
theorem checked1071 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1071 (maskNeeds ![1237940335011998006369059201, 151152620940525821756930, 75576310469988032976900, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq1071]
  exact B1071.sound accepted1071
#print axioms checked1071

def B1374 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1374 : B1374.tree = HexagonCover.NBand.M8500_8700.SplitData.node1374 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1373 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1374, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1373 : B1373.tree = HexagonCover.NBand.M8500_8700.SplitData.node1373 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1374
  · rfl

def B1372 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1373]
theorem treeEq1372 : B1372.tree = HexagonCover.NBand.M8500_8700.SplitData.node1372 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1373

def B1371 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1372, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq1371 : B1371.tree = HexagonCover.NBand.M8500_8700.SplitData.node1371 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1372
  · rfl
  · rfl
  · rfl

def B1370 : Block := .branch 159 ![5192298715444887135313460795015553, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 363).pointIds 363), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1371]
theorem treeEq1370 : B1370.tree = HexagonCover.NBand.M8500_8700.SplitData.node1370 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1371

def B1380 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1380 : B1380.tree = HexagonCover.NBand.M8500_8700.SplitData.node1380 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1379 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1380, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1379 : B1379.tree = HexagonCover.NBand.M8500_8700.SplitData.node1379 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1380
  · rfl

def B1378 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1379]
theorem treeEq1378 : B1378.tree = HexagonCover.NBand.M8500_8700.SplitData.node1378 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1379

def B1377 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1378, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1377 : B1377.tree = HexagonCover.NBand.M8500_8700.SplitData.node1377 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1378
  · rfl
  · rfl
  · rfl

def B1376 : Block := .branch 159 ![10385863224579942993245453827441025, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1377]
theorem treeEq1376 : B1376.tree = HexagonCover.NBand.M8500_8700.SplitData.node1376 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1377

def B1384 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1384 : B1384.tree = HexagonCover.NBand.M8500_8700.SplitData.node1384 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1383 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1384, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1383 : B1383.tree = HexagonCover.NBand.M8500_8700.SplitData.node1383 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1384
  · rfl

def B1382 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1383]
theorem treeEq1382 : B1382.tree = HexagonCover.NBand.M8500_8700.SplitData.node1382 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1383

def B1381 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1382, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1381 : B1381.tree = HexagonCover.NBand.M8500_8700.SplitData.node1381 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1382
  · rfl
  · rfl
  · rfl

def B1375 : Block := .branch 113 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B1376, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1381]
theorem treeEq1375 : B1375.tree = HexagonCover.NBand.M8500_8700.SplitData.node1375 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1376
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1381

def B1369 : Block := .branch 112 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B1370, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1375]
theorem treeEq1369 : B1369.tree = HexagonCover.NBand.M8500_8700.SplitData.node1369 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1370
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1375

def B1386 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1386 : B1386.tree = HexagonCover.NBand.M8500_8700.SplitData.node1386 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1385 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1386, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1385 : B1385.tree = HexagonCover.NBand.M8500_8700.SplitData.node1385 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1386
  · rfl

def B1368 : Block := .branch 109 ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B1369, (.leaf 5 (Common.fact 294).pointIds 294), B1385]
theorem treeEq1368 : B1368.tree = HexagonCover.NBand.M8500_8700.SplitData.node1368 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1369
  · rfl
  · exact treeEq1385

theorem accepted1368 : B1368.accepted = true := by decide +kernel
theorem checked1368 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1368 (maskNeeds ![1269507510287736184461169000833, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1368]
  exact B1368.sound accepted1368
#print axioms checked1368

def B1408 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1408 : B1408.tree = HexagonCover.NBand.M8500_8700.SplitData.node1408 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1407 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325905467305191218409773667103624659008] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1408, (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1407 : B1407.tree = HexagonCover.NBand.M8500_8700.SplitData.node1407 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1408
  · rfl

def B1406 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1407]
theorem treeEq1406 : B1406.tree = HexagonCover.NBand.M8500_8700.SplitData.node1406 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1407

def B1405 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1406, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq1405 : B1405.tree = HexagonCover.NBand.M8500_8700.SplitData.node1405 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1406
  · rfl
  · rfl
  · rfl

def B1404 : Block := .branch 159 ![5193565747377327176928477342335361, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 738).pointIds 738), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1405]
theorem treeEq1404 : B1404.tree = HexagonCover.NBand.M8500_8700.SplitData.node1404 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1405

def B1414 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1414 : B1414.tree = HexagonCover.NBand.M8500_8700.SplitData.node1414 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1413 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993886115266325910659602049753237402197599953879104] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1414, (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1413 : B1413.tree = HexagonCover.NBand.M8500_8700.SplitData.node1413 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1414
  · rfl

def B1412 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1413]
theorem treeEq1412 : B1412.tree = HexagonCover.NBand.M8500_8700.SplitData.node1412 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1413

def B1411 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 730762012636734178455512350289777942250105864256] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1412, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1411 : B1411.tree = HexagonCover.NBand.M8500_8700.SplitData.node1411 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1412
  · rfl
  · rfl
  · rfl

def B1410 : Block := .branch 159 ![10385862605912154805458973671555457, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![(.leaf 0 (Common.fact 756).pointIds 756), (.leaf 1 (Common.fact 900).pointIds 900), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B1411]
theorem treeEq1410 : B1410.tree = HexagonCover.NBand.M8500_8700.SplitData.node1410 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1411

def B1418 : Block := .branch 169 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 907).pointIds 907), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 822).pointIds 822), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1418 : B1418.tree = HexagonCover.NBand.M8500_8700.SplitData.node1418 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1417 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660464392797065871706889218268316827712] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1418, (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1417 : B1417.tree = HexagonCover.NBand.M8500_8700.SplitData.node1417 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1418
  · rfl

def B1416 : Block := .branch 171 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 5986310706507378353287286997439407561319416980332552, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 818).pointIds 818), (.leaf 3 (Common.fact 670).pointIds 670), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B1417]
theorem treeEq1416 : B1416.tree = HexagonCover.NBand.M8500_8700.SplitData.node1416 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1417

def B1415 : Block := .branch 172 ![1237940039864092827016233345, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971287911650528468759264962918468812864] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 868).pointIds 868), B1416, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq1415 : B1415.tree = HexagonCover.NBand.M8500_8700.SplitData.node1415 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1416
  · rfl
  · rfl
  · rfl

def B1409 : Block := .branch 113 ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971282719353669933931636432422139592768] ![B1410, (.leaf 1 (Common.fact 300).pointIds 300), (.leaf 2 (Common.fact 301).pointIds 301), (.leaf 3 (Common.fact 302).pointIds 302), (.leaf 4 (Common.fact 303).pointIds 303), (.leaf 5 (Common.fact 304).pointIds 304), B1415]
theorem treeEq1409 : B1409.tree = HexagonCover.NBand.M8500_8700.SplitData.node1409 := by
  change Tree.branch (113 : Fin 175) _ = Tree.branch (113 : Fin 175) _
  apply congrArg (Tree.branch (113 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1410
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1415

def B1403 : Block := .branch 112 ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 324993922633512312808717284302856, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![B1404, (.leaf 1 (Common.fact 295).pointIds 295), (.leaf 2 (Common.fact 296).pointIds 296), (.leaf 3 (Common.fact 297).pointIds 297), (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), B1409]
theorem treeEq1403 : B1403.tree = HexagonCover.NBand.M8500_8700.SplitData.node1403 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq1404
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1409

def B1420 : Block := .branch 168 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 765).pointIds 765), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1420 : B1420.tree = HexagonCover.NBand.M8500_8700.SplitData.node1420 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1419 : Block := .branch 170 ![1237940039864092827016233345, 151447768845705174582786, 37778931862957161715716, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11193971278176093918715957461468237851525184] ![(.leaf 0 (Common.fact 905).pointIds 905), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 820).pointIds 820), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B1420, (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1419 : B1419.tree = HexagonCover.NBand.M8500_8700.SplitData.node1419 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1420
  · rfl

def B1402 : Block := .branch 109 ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 290).pointIds 290), (.leaf 1 (Common.fact 291).pointIds 291), (.leaf 2 (Common.fact 292).pointIds 292), (.leaf 3 (Common.fact 293).pointIds 293), B1403, (.leaf 5 (Common.fact 294).pointIds 294), B1419]
theorem treeEq1402 : B1402.tree = HexagonCover.NBand.M8500_8700.SplitData.node1402 := by
  change Tree.branch (109 : Fin 175) _ = Tree.branch (109 : Fin 175) _
  apply congrArg (Tree.branch (109 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1403
  · rfl
  · exact treeEq1419

theorem accepted1402 : B1402.accepted = true := by decide +kernel
theorem checked1402 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node1402 (maskNeeds ![1268888842499548397981013115265, 151447768845705174582786, 4873482210321473860540420, 325073150796026577146310828253192, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq1402]
  exact B1402.sound accepted1402
#print axioms checked1402

end HexagonCover.NBand.M8500_8700.SplitTree.Run0018
