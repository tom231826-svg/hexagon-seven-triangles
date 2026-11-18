import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0014
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0015
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1107_1124 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1124 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] HexagonCover.NBand.M6667_6700.SplitTree.Run0014.checked1124
def B1112 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1112 : B1112.tree = HexagonCover.NBand.M6667_6700.SplitData.node1112 := by
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

def B1111 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1112, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1111 : B1111.tree = HexagonCover.NBand.M6667_6700.SplitData.node1111 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112
  · rfl
  · rfl

def B1110 : Block := .branch 158 ![10636420114708594398197643235014214017, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1111]
theorem treeEq1110 : B1110.tree = HexagonCover.NBand.M6667_6700.SplitData.node1110 := by
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
  · exact treeEq1111

def B1115 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1115 : B1115.tree = HexagonCover.NBand.M6667_6700.SplitData.node1115 := by
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

def B1114 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1115]
theorem treeEq1114 : B1114.tree = HexagonCover.NBand.M6667_6700.SplitData.node1114 := by
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
  · exact treeEq1115

def B1113 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1114, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1113 : B1113.tree = HexagonCover.NBand.M6667_6700.SplitData.node1113 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1114
  · rfl
  · rfl

def B1109 : Block := .branch 123 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1110, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1113]
theorem treeEq1109 : B1109.tree = HexagonCover.NBand.M6667_6700.SplitData.node1109 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1110
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1113

def B1120 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1120 : B1120.tree = HexagonCover.NBand.M6667_6700.SplitData.node1120 := by
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

def B1119 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1120, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1119 : B1119.tree = HexagonCover.NBand.M6667_6700.SplitData.node1119 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1120
  · rfl
  · rfl

def B1118 : Block := .branch 158 ![10636420114708594398197643235014214017, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1119]
theorem treeEq1118 : B1118.tree = HexagonCover.NBand.M6667_6700.SplitData.node1118 := by
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
  · exact treeEq1119

def B1123 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1123 : B1123.tree = HexagonCover.NBand.M6667_6700.SplitData.node1123 := by
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

def B1122 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1123]
theorem treeEq1122 : B1122.tree = HexagonCover.NBand.M6667_6700.SplitData.node1122 := by
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
  · exact treeEq1123

def B1121 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1122, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1121 : B1121.tree = HexagonCover.NBand.M6667_6700.SplitData.node1121 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1122
  · rfl
  · rfl

def B1117 : Block := .branch 123 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1118, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1121]
theorem treeEq1117 : B1117.tree = HexagonCover.NBand.M6667_6700.SplitData.node1117 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1118
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1121

def B1116 : Block := .branch 73 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), B1117, Tip1107_1124, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 1026).pointIds 1026)]
theorem treeEq1116 : B1116.tree = HexagonCover.NBand.M6667_6700.SplitData.node1116 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1117
  · rfl
  · rfl
  · rfl
  · rfl

def B1108 : Block := .branch 72 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B1109, B1116, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq1108 : B1108.tree = HexagonCover.NBand.M6667_6700.SplitData.node1108 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1109
  · exact treeEq1116
  · rfl
  · rfl
  · rfl

def B1107 : Block := .branch 140 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1108, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1107 : B1107.tree = HexagonCover.NBand.M6667_6700.SplitData.node1107 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1108
  · rfl
  · rfl

theorem accepted1107 : B1107.accepted = true := by decide +kernel
theorem checked1107 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1107 (maskNeeds ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq1107]
  exact B1107.sound accepted1107
#print axioms checked1107

def B1143 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1143 : B1143.tree = HexagonCover.NBand.M6667_6700.SplitData.node1143 := by
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

def B1142 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1143]
theorem treeEq1142 : B1142.tree = HexagonCover.NBand.M6667_6700.SplitData.node1142 := by
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
  · exact treeEq1143

def B1146 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1146 : B1146.tree = HexagonCover.NBand.M6667_6700.SplitData.node1146 := by
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

def B1145 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1146]
theorem treeEq1145 : B1145.tree = HexagonCover.NBand.M6667_6700.SplitData.node1145 := by
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
  · exact treeEq1146

def B1144 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1145, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1144 : B1144.tree = HexagonCover.NBand.M6667_6700.SplitData.node1144 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1145
  · rfl
  · rfl

def B1141 : Block := .branch 119 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1142, (.leaf 5 (Common.fact 419).pointIds 419), B1144]
theorem treeEq1141 : B1141.tree = HexagonCover.NBand.M6667_6700.SplitData.node1141 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1142
  · rfl
  · exact treeEq1144

def B1148 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1148 : B1148.tree = HexagonCover.NBand.M6667_6700.SplitData.node1148 := by
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

def B1147 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1148, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1147 : B1147.tree = HexagonCover.NBand.M6667_6700.SplitData.node1147 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1148
  · rfl
  · rfl

def B1140 : Block := .branch 112 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1141, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1147]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M6667_6700.SplitData.node1140 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1141
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1147

def B1152 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1152 : B1152.tree = HexagonCover.NBand.M6667_6700.SplitData.node1152 := by
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

def B1151 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1152]
theorem treeEq1151 : B1151.tree = HexagonCover.NBand.M6667_6700.SplitData.node1151 := by
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
  · exact treeEq1152

def B1155 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1155 : B1155.tree = HexagonCover.NBand.M6667_6700.SplitData.node1155 := by
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

def B1154 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1155]
theorem treeEq1154 : B1154.tree = HexagonCover.NBand.M6667_6700.SplitData.node1154 := by
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
  · exact treeEq1155

def B1153 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1154, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1153 : B1153.tree = HexagonCover.NBand.M6667_6700.SplitData.node1153 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1154
  · rfl
  · rfl

def B1150 : Block := .branch 119 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1151, (.leaf 5 (Common.fact 419).pointIds 419), B1153]
theorem treeEq1150 : B1150.tree = HexagonCover.NBand.M6667_6700.SplitData.node1150 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1151
  · rfl
  · exact treeEq1153

def B1157 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M6667_6700.SplitData.node1157 := by
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

def B1156 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1157, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1156 : B1156.tree = HexagonCover.NBand.M6667_6700.SplitData.node1156 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1157
  · rfl
  · rfl

def B1149 : Block := .branch 112 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1150, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1156]
theorem treeEq1149 : B1149.tree = HexagonCover.NBand.M6667_6700.SplitData.node1149 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1150
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1156

def B1139 : Block := .branch 72 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B1140, B1149, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M6667_6700.SplitData.node1139 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1140
  · exact treeEq1149
  · rfl
  · rfl
  · rfl

theorem accepted1139 : B1139.accepted = true := by decide +kernel
theorem checked1139 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1139 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520]) := by
  rw [← treeEq1139]
  exact B1139.sound accepted1139
#print axioms checked1139

def Tip1091_1107 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1107 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] checked1107
def Tip1091_1139 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1139 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] checked1139
def B1094 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq1094 : B1094.tree = HexagonCover.NBand.M6667_6700.SplitData.node1094 := by
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

def B1093 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1094]
theorem treeEq1093 : B1093.tree = HexagonCover.NBand.M6667_6700.SplitData.node1093 := by
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
  · exact treeEq1094

def B1097 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq1097 : B1097.tree = HexagonCover.NBand.M6667_6700.SplitData.node1097 := by
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

def B1096 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B1097]
theorem treeEq1096 : B1096.tree = HexagonCover.NBand.M6667_6700.SplitData.node1096 := by
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
  · exact treeEq1097

def B1100 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq1100 : B1100.tree = HexagonCover.NBand.M6667_6700.SplitData.node1100 := by
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

def B1099 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1100]
theorem treeEq1099 : B1099.tree = HexagonCover.NBand.M6667_6700.SplitData.node1099 := by
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
  · exact treeEq1100

def B1106 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq1106 : B1106.tree = HexagonCover.NBand.M6667_6700.SplitData.node1106 := by
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

def B1105 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1106, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq1105 : B1105.tree = HexagonCover.NBand.M6667_6700.SplitData.node1105 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1106
  · rfl
  · rfl

def B1104 : Block := .branch 158 ![5319508131568930906582414993892835713, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 542).pointIds 542), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1105]
theorem treeEq1104 : B1104.tree = HexagonCover.NBand.M6667_6700.SplitData.node1104 := by
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
  · exact treeEq1105

def B1103 : Block := .branch 140 ![5319508131568930906582414993892835713, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1104, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq1103 : B1103.tree = HexagonCover.NBand.M6667_6700.SplitData.node1103 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1104
  · rfl
  · rfl

def B1102 : Block := .branch 163 ![5319508131568930906582414993892835713, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1103]
theorem treeEq1102 : B1102.tree = HexagonCover.NBand.M6667_6700.SplitData.node1102 := by
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
  · exact treeEq1103

def B1101 : Block := .branch 122 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B1102, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip1091_1107]
theorem treeEq1101 : B1101.tree = HexagonCover.NBand.M6667_6700.SplitData.node1101 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1102
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1098 : Block := .branch 121 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1099, (.leaf 5 (Common.fact 430).pointIds 430), B1101]
theorem treeEq1098 : B1098.tree = HexagonCover.NBand.M6667_6700.SplitData.node1098 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1099
  · rfl
  · exact treeEq1101

def B1095 : Block := .branch 120 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1096, (.leaf 5 (Common.fact 163).pointIds 163), B1098]
theorem treeEq1095 : B1095.tree = HexagonCover.NBand.M6667_6700.SplitData.node1095 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1096
  · rfl
  · exact treeEq1098

def B1092 : Block := .branch 119 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1093, (.leaf 5 (Common.fact 419).pointIds 419), B1095]
theorem treeEq1092 : B1092.tree = HexagonCover.NBand.M6667_6700.SplitData.node1092 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1093
  · rfl
  · exact treeEq1095

def B1091 : Block := .branch 111 ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![B1092, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip1091_1139]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M6667_6700.SplitData.node1091 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1092
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1091 : B1091.accepted = true := by decide +kernel
theorem checked1091 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1091 (maskNeeds ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184]) := by
  rw [← treeEq1091]
  exact B1091.sound accepted1091
#print axioms checked1091

def Tip0918_0934 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0934 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] HexagonCover.NBand.M6667_6700.SplitTree.Run0014.checked0934
def Tip0918_1072 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1072 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] HexagonCover.NBand.M6667_6700.SplitTree.Run0014.checked1072
def Tip0918_1091 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1091 ![1152921504606847361, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] checked1091
def B0922 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1010).pointIds 1010)]
theorem treeEq0922 : B0922.tree = HexagonCover.NBand.M6667_6700.SplitData.node0922 := by
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

def B0921 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 324518553658426726783156020674576, 393248, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B0922, (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq0921 : B0921.tree = HexagonCover.NBand.M6667_6700.SplitData.node0921 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0922
  · rfl

def B0920 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 324518553658426726783156020674576, 393248, 6360455125664089500023387129931434873594290709725248] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B0921]
theorem treeEq0920 : B0920.tree = HexagonCover.NBand.M6667_6700.SplitData.node0920 := by
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
  · exact treeEq0921

def B0927 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq0927 : B0927.tree = HexagonCover.NBand.M6667_6700.SplitData.node0927 := by
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

def B0926 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B0927]
theorem treeEq0926 : B0926.tree = HexagonCover.NBand.M6667_6700.SplitData.node0926 := by
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
  · exact treeEq0927

def B0930 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0930 : B0930.tree = HexagonCover.NBand.M6667_6700.SplitData.node0930 := by
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

def B0929 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B0930]
theorem treeEq0929 : B0929.tree = HexagonCover.NBand.M6667_6700.SplitData.node0929 := by
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
  · exact treeEq0930

def B0933 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq0933 : B0933.tree = HexagonCover.NBand.M6667_6700.SplitData.node0933 := by
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

def B0932 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B0933]
theorem treeEq0932 : B0932.tree = HexagonCover.NBand.M6667_6700.SplitData.node0932 := by
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
  · exact treeEq0933

def B0931 : Block := .branch 121 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664091495487973575597377863220661233123392] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B0932, (.leaf 5 (Common.fact 430).pointIds 430), Tip0918_0934]
theorem treeEq0931 : B0931.tree = HexagonCover.NBand.M6667_6700.SplitData.node0931 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0932
  · rfl
  · rfl

def B0928 : Block := .branch 120 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664090166259977790681504959413600952778816] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B0929, (.leaf 5 (Common.fact 163).pointIds 163), B0931]
theorem treeEq0928 : B0928.tree = HexagonCover.NBand.M6667_6700.SplitData.node0928 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0929
  · rfl
  · exact treeEq0931

def B0925 : Block := .branch 119 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898223568507510070812606528] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B0926, (.leaf 5 (Common.fact 419).pointIds 419), B0928]
theorem treeEq0925 : B0925.tree = HexagonCover.NBand.M6667_6700.SplitData.node0925 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0926
  · rfl
  · exact treeEq0928

def B0924 : Block := .branch 111 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![B0925, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip0918_1072]
theorem treeEq0924 : B0924.tree = HexagonCover.NBand.M6667_6700.SplitData.node0924 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0925
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0923 : Block := .branch 69 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898223568507510070812606528] ![B0924, Tip0918_1091, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1011).pointIds 1011)]
theorem treeEq0923 : B0923.tree = HexagonCover.NBand.M6667_6700.SplitData.node0923 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0924
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0919 : Block := .branch 108 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B0920, (.leaf 5 (Common.fact 136).pointIds 136), B0923]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M6667_6700.SplitData.node0919 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0920
  · rfl
  · exact treeEq0923

def B1161 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M6667_6700.SplitData.node1161 := by
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

def B1160 : Block := .branch 170 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 1002).pointIds 1002), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 1003).pointIds 1003), (.leaf 3 (Common.fact 1004).pointIds 1004), (.leaf 4 (Common.fact 1005).pointIds 1005), B1161, (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M6667_6700.SplitData.node1160 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1161
  · rfl

def B1159 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605831777217696535764533312] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B1160]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M6667_6700.SplitData.node1159 := by
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
  · exact treeEq1160

def B1158 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820465484124829159846838336] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1159, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M6667_6700.SplitData.node1158 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1159
  · rfl
  · rfl

def B0918 : Block := .branch 101 ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272] ![B0919, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B1158]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M6667_6700.SplitData.node0918 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0919
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1158

theorem accepted0918 : B0918.accepted = true := by decide +kernel
theorem checked0918 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0918 (maskNeeds ![1152921504606847361, 618970167216643826637604354, 36893488147419109380, 19345174297075501617930248, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq0918]
  exact B0918.sound accepted0918
#print axioms checked0918

end HexagonCover.NBand.M6667_6700.SplitTree.Run0015
