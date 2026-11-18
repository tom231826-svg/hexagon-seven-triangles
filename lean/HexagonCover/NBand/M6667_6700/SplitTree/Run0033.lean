import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0032
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0033
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2417_2434 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2434 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] HexagonCover.NBand.M6667_6700.SplitTree.Run0032.checked2434
def B2423 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2423 : B2423.tree = HexagonCover.NBand.M6667_6700.SplitData.node2423 := by
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

def B2422 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2423, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2422 : B2422.tree = HexagonCover.NBand.M6667_6700.SplitData.node2422 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2423
  · rfl
  · rfl

def B2421 : Block := .branch 158 ![10636420115946534436330102005306491265, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1199).pointIds 1199), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2422]
theorem treeEq2421 : B2421.tree = HexagonCover.NBand.M6667_6700.SplitData.node2421 := by
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
  · exact treeEq2422

def B2426 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2426 : B2426.tree = HexagonCover.NBand.M6667_6700.SplitData.node2426 := by
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

def B2425 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2426]
theorem treeEq2425 : B2425.tree = HexagonCover.NBand.M6667_6700.SplitData.node2425 := by
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
  · exact treeEq2426

def B2424 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2425, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2424 : B2424.tree = HexagonCover.NBand.M6667_6700.SplitData.node2424 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2425
  · rfl
  · rfl

def B2420 : Block := .branch 123 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2421, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2424]
theorem treeEq2420 : B2420.tree = HexagonCover.NBand.M6667_6700.SplitData.node2420 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2421
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2424

def B2430 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2430 : B2430.tree = HexagonCover.NBand.M6667_6700.SplitData.node2430 := by
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

def B2429 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2430, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2429 : B2429.tree = HexagonCover.NBand.M6667_6700.SplitData.node2429 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2430
  · rfl
  · rfl

def B2428 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2429]
theorem treeEq2428 : B2428.tree = HexagonCover.NBand.M6667_6700.SplitData.node2428 := by
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
  · exact treeEq2429

def B2433 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2433 : B2433.tree = HexagonCover.NBand.M6667_6700.SplitData.node2433 := by
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

def B2432 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2433]
theorem treeEq2432 : B2432.tree = HexagonCover.NBand.M6667_6700.SplitData.node2432 := by
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
  · exact treeEq2433

def B2431 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2432, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2431 : B2431.tree = HexagonCover.NBand.M6667_6700.SplitData.node2431 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2432
  · rfl
  · rfl

def B2427 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2428, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2431]
theorem treeEq2427 : B2427.tree = HexagonCover.NBand.M6667_6700.SplitData.node2427 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2428
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2431

def B2419 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![B2420, B2427, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq2419 : B2419.tree = HexagonCover.NBand.M6667_6700.SplitData.node2419 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2420
  · exact treeEq2427
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2418 : Block := .branch 72 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B2419, Tip2417_2434, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq2418 : B2418.tree = HexagonCover.NBand.M6667_6700.SplitData.node2418 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2419
  · rfl
  · rfl
  · rfl
  · rfl

def B2417 : Block := .branch 140 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2418, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq2417 : B2417.tree = HexagonCover.NBand.M6667_6700.SplitData.node2417 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2418
  · rfl
  · rfl

theorem accepted2417 : B2417.accepted = true := by decide +kernel
theorem checked2417 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2417 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2417]
  exact B2417.sound accepted2417
#print axioms checked2417

def Tip2361_2373 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2373 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] HexagonCover.NBand.M6667_6700.SplitTree.Run0032.checked2373
def B2363 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2363 : B2363.tree = HexagonCover.NBand.M6667_6700.SplitData.node2363 := by
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

def B2362 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B2363]
theorem treeEq2362 : B2362.tree = HexagonCover.NBand.M6667_6700.SplitData.node2362 := by
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
  · exact treeEq2363

def B2366 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq2366 : B2366.tree = HexagonCover.NBand.M6667_6700.SplitData.node2366 := by
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

def B2365 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2366]
theorem treeEq2365 : B2365.tree = HexagonCover.NBand.M6667_6700.SplitData.node2365 := by
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
  · exact treeEq2366

def B2372 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq2372 : B2372.tree = HexagonCover.NBand.M6667_6700.SplitData.node2372 := by
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

def B2371 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2372, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2371 : B2371.tree = HexagonCover.NBand.M6667_6700.SplitData.node2371 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2372
  · rfl
  · rfl

def B2370 : Block := .branch 158 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1190).pointIds 1190), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2371]
theorem treeEq2370 : B2370.tree = HexagonCover.NBand.M6667_6700.SplitData.node2370 := by
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
  · exact treeEq2371

def B2369 : Block := .branch 140 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2370, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq2369 : B2369.tree = HexagonCover.NBand.M6667_6700.SplitData.node2369 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2370
  · rfl
  · rfl

def B2368 : Block := .branch 163 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1189).pointIds 1189), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2369]
theorem treeEq2368 : B2368.tree = HexagonCover.NBand.M6667_6700.SplitData.node2368 := by
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
  · exact treeEq2369

def B2367 : Block := .branch 122 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B2368, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2361_2373]
theorem treeEq2367 : B2367.tree = HexagonCover.NBand.M6667_6700.SplitData.node2367 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2364 : Block := .branch 121 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2365, (.leaf 5 (Common.fact 430).pointIds 430), B2367]
theorem treeEq2364 : B2364.tree = HexagonCover.NBand.M6667_6700.SplitData.node2364 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2365
  · rfl
  · exact treeEq2367

def B2361 : Block := .branch 120 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2362, (.leaf 5 (Common.fact 163).pointIds 163), B2364]
theorem treeEq2361 : B2361.tree = HexagonCover.NBand.M6667_6700.SplitData.node2361 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2362
  · rfl
  · exact treeEq2364

theorem accepted2361 : B2361.accepted = true := by decide +kernel
theorem checked2361 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2361 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216]) := by
  rw [← treeEq2361]
  exact B2361.sound accepted2361
#print axioms checked2361

def B2485 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq2485 : B2485.tree = HexagonCover.NBand.M6667_6700.SplitData.node2485 := by
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

def B2484 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2485]
theorem treeEq2484 : B2484.tree = HexagonCover.NBand.M6667_6700.SplitData.node2484 := by
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
  · exact treeEq2485

def B2488 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2488 : B2488.tree = HexagonCover.NBand.M6667_6700.SplitData.node2488 := by
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

def B2487 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2488]
theorem treeEq2487 : B2487.tree = HexagonCover.NBand.M6667_6700.SplitData.node2487 := by
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
  · exact treeEq2488

def B2486 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2487, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq2486 : B2486.tree = HexagonCover.NBand.M6667_6700.SplitData.node2486 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2487
  · rfl
  · rfl

def B2483 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2484, (.leaf 5 (Common.fact 419).pointIds 419), B2486]
theorem treeEq2483 : B2483.tree = HexagonCover.NBand.M6667_6700.SplitData.node2483 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2484
  · rfl
  · exact treeEq2486

def B2490 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2490 : B2490.tree = HexagonCover.NBand.M6667_6700.SplitData.node2490 := by
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

def B2489 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2490, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq2489 : B2489.tree = HexagonCover.NBand.M6667_6700.SplitData.node2489 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2490
  · rfl
  · rfl

def B2482 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B2483, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2489]
theorem treeEq2482 : B2482.tree = HexagonCover.NBand.M6667_6700.SplitData.node2482 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2483
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2489

def B2494 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq2494 : B2494.tree = HexagonCover.NBand.M6667_6700.SplitData.node2494 := by
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

def B2493 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2494]
theorem treeEq2493 : B2493.tree = HexagonCover.NBand.M6667_6700.SplitData.node2493 := by
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
  · exact treeEq2494

def B2497 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2497 : B2497.tree = HexagonCover.NBand.M6667_6700.SplitData.node2497 := by
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

def B2496 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2497]
theorem treeEq2496 : B2496.tree = HexagonCover.NBand.M6667_6700.SplitData.node2496 := by
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
  · exact treeEq2497

def B2495 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2496, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq2495 : B2495.tree = HexagonCover.NBand.M6667_6700.SplitData.node2495 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2496
  · rfl
  · rfl

def B2492 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2493, (.leaf 5 (Common.fact 419).pointIds 419), B2495]
theorem treeEq2492 : B2492.tree = HexagonCover.NBand.M6667_6700.SplitData.node2492 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2493
  · rfl
  · exact treeEq2495

def B2499 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq2499 : B2499.tree = HexagonCover.NBand.M6667_6700.SplitData.node2499 := by
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

def B2498 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2499, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq2498 : B2498.tree = HexagonCover.NBand.M6667_6700.SplitData.node2498 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2499
  · rfl
  · rfl

def B2491 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B2492, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2498]
theorem treeEq2491 : B2491.tree = HexagonCover.NBand.M6667_6700.SplitData.node2491 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2492
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2498

def B2481 : Block := .branch 72 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B2482, B2491, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq2481 : B2481.tree = HexagonCover.NBand.M6667_6700.SplitData.node2481 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2482
  · exact treeEq2491
  · rfl
  · rfl
  · rfl

theorem accepted2481 : B2481.accepted = true := by decide +kernel
theorem checked2481 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2481 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520]) := by
  rw [← treeEq2481]
  exact B2481.sound accepted2481
#print axioms checked2481

def Tip2356_2417 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2417 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] checked2417
def Tip2356_2361 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2361 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] checked2361
def Tip2356_2481 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2481 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] checked2481
def B2359 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq2359 : B2359.tree = HexagonCover.NBand.M6667_6700.SplitData.node2359 := by
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

def B2358 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2359]
theorem treeEq2358 : B2358.tree = HexagonCover.NBand.M6667_6700.SplitData.node2358 := by
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
  · exact treeEq2359

def B2407 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2407 : B2407.tree = HexagonCover.NBand.M6667_6700.SplitData.node2407 := by
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

def B2406 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B2407]
theorem treeEq2406 : B2406.tree = HexagonCover.NBand.M6667_6700.SplitData.node2406 := by
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
  · exact treeEq2407

def B2410 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq2410 : B2410.tree = HexagonCover.NBand.M6667_6700.SplitData.node2410 := by
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

def B2409 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2410]
theorem treeEq2409 : B2409.tree = HexagonCover.NBand.M6667_6700.SplitData.node2409 := by
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
  · exact treeEq2410

def B2416 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq2416 : B2416.tree = HexagonCover.NBand.M6667_6700.SplitData.node2416 := by
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

def B2415 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2416, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2415 : B2415.tree = HexagonCover.NBand.M6667_6700.SplitData.node2415 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2416
  · rfl
  · rfl

def B2414 : Block := .branch 158 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1193).pointIds 1193), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2415]
theorem treeEq2414 : B2414.tree = HexagonCover.NBand.M6667_6700.SplitData.node2414 := by
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
  · exact treeEq2415

def B2413 : Block := .branch 140 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2414, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq2413 : B2413.tree = HexagonCover.NBand.M6667_6700.SplitData.node2413 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2414
  · rfl
  · rfl

def B2412 : Block := .branch 163 ![5319508131568930905429493489285988737, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1192).pointIds 1192), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2413]
theorem treeEq2412 : B2412.tree = HexagonCover.NBand.M6667_6700.SplitData.node2412 := by
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
  · exact treeEq2413

def B2411 : Block := .branch 122 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B2412, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2356_2417]
theorem treeEq2411 : B2411.tree = HexagonCover.NBand.M6667_6700.SplitData.node2411 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2412
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2408 : Block := .branch 121 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2409, (.leaf 5 (Common.fact 430).pointIds 430), B2411]
theorem treeEq2408 : B2408.tree = HexagonCover.NBand.M6667_6700.SplitData.node2408 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2409
  · rfl
  · exact treeEq2411

def B2405 : Block := .branch 120 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2406, (.leaf 5 (Common.fact 163).pointIds 163), B2408]
theorem treeEq2405 : B2405.tree = HexagonCover.NBand.M6667_6700.SplitData.node2405 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2406
  · rfl
  · exact treeEq2408

def B2360 : Block := .branch 79 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![Tip2356_2361, B2405, (.leaf 2 (Common.fact 1184).pointIds 1184), (.leaf 3 (Common.fact 1185).pointIds 1185), (.leaf 4 (Common.fact 1186).pointIds 1186), (.leaf 5 (Common.fact 1187).pointIds 1187), (.leaf 6 (Common.fact 1188).pointIds 1188)]
theorem treeEq2360 : B2360.tree = HexagonCover.NBand.M6667_6700.SplitData.node2360 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2405
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2357 : Block := .branch 119 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2358, (.leaf 5 (Common.fact 419).pointIds 419), B2360]
theorem treeEq2357 : B2357.tree = HexagonCover.NBand.M6667_6700.SplitData.node2357 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2358
  · rfl
  · exact treeEq2360

def B2356 : Block := .branch 111 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![B2357, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip2356_2481]
theorem treeEq2356 : B2356.tree = HexagonCover.NBand.M6667_6700.SplitData.node2356 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2357
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2356 : B2356.accepted = true := by decide +kernel
theorem checked2356 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2356 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184]) := by
  rw [← treeEq2356]
  exact B2356.sound accepted2356
#print axioms checked2356

end HexagonCover.NBand.M6667_6700.SplitTree.Run0033
