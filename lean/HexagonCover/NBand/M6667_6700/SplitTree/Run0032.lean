import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0032
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B2394 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2394 : B2394.tree = HexagonCover.NBand.M6667_6700.SplitData.node2394 := by
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

def B2393 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2394, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2393 : B2393.tree = HexagonCover.NBand.M6667_6700.SplitData.node2393 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2394
  · rfl
  · rfl

def B2392 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2393]
theorem treeEq2392 : B2392.tree = HexagonCover.NBand.M6667_6700.SplitData.node2392 := by
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
  · exact treeEq2393

def B2397 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2397 : B2397.tree = HexagonCover.NBand.M6667_6700.SplitData.node2397 := by
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

def B2396 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2397]
theorem treeEq2396 : B2396.tree = HexagonCover.NBand.M6667_6700.SplitData.node2396 := by
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
  · exact treeEq2397

def B2395 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2396, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2395 : B2395.tree = HexagonCover.NBand.M6667_6700.SplitData.node2395 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2396
  · rfl
  · rfl

def B2391 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2392, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2395]
theorem treeEq2391 : B2391.tree = HexagonCover.NBand.M6667_6700.SplitData.node2391 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2392
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2395

def B2401 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2401 : B2401.tree = HexagonCover.NBand.M6667_6700.SplitData.node2401 := by
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

def B2400 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2401, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2400 : B2400.tree = HexagonCover.NBand.M6667_6700.SplitData.node2400 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2401
  · rfl
  · rfl

def B2399 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2400]
theorem treeEq2399 : B2399.tree = HexagonCover.NBand.M6667_6700.SplitData.node2399 := by
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
  · exact treeEq2400

def B2404 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2404 : B2404.tree = HexagonCover.NBand.M6667_6700.SplitData.node2404 := by
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

def B2403 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2404]
theorem treeEq2403 : B2403.tree = HexagonCover.NBand.M6667_6700.SplitData.node2403 := by
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
  · exact treeEq2404

def B2402 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2403, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2402 : B2402.tree = HexagonCover.NBand.M6667_6700.SplitData.node2402 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2403
  · rfl
  · rfl

def B2398 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2399, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2402]
theorem treeEq2398 : B2398.tree = HexagonCover.NBand.M6667_6700.SplitData.node2398 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2399
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2402

def B2390 : Block := .branch 74 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2391, B2398, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1027).pointIds 1027)]
theorem treeEq2390 : B2390.tree = HexagonCover.NBand.M6667_6700.SplitData.node2390 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2391
  · exact treeEq2398
  · rfl
  · rfl
  · rfl

theorem accepted2390 : B2390.accepted = true := by decide +kernel
theorem checked2390 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2390 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2390]
  exact B2390.sound accepted2390
#print axioms checked2390

def Tip2373_2390 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2390 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] checked2390
def B2378 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2378 : B2378.tree = HexagonCover.NBand.M6667_6700.SplitData.node2378 := by
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

def B2377 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2378, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2377 : B2377.tree = HexagonCover.NBand.M6667_6700.SplitData.node2377 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2378
  · rfl
  · rfl

def B2376 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2377]
theorem treeEq2376 : B2376.tree = HexagonCover.NBand.M6667_6700.SplitData.node2376 := by
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
  · exact treeEq2377

def B2381 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2381 : B2381.tree = HexagonCover.NBand.M6667_6700.SplitData.node2381 := by
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

def B2380 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2381]
theorem treeEq2380 : B2380.tree = HexagonCover.NBand.M6667_6700.SplitData.node2380 := by
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
  · exact treeEq2381

def B2379 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2380, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2379 : B2379.tree = HexagonCover.NBand.M6667_6700.SplitData.node2379 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2380
  · rfl
  · rfl

def B2375 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2376, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2379]
theorem treeEq2375 : B2375.tree = HexagonCover.NBand.M6667_6700.SplitData.node2375 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2376
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2379

def B2386 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2386 : B2386.tree = HexagonCover.NBand.M6667_6700.SplitData.node2386 := by
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

def B2385 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2386, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2385 : B2385.tree = HexagonCover.NBand.M6667_6700.SplitData.node2385 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2386
  · rfl
  · rfl

def B2384 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2385]
theorem treeEq2384 : B2384.tree = HexagonCover.NBand.M6667_6700.SplitData.node2384 := by
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
  · exact treeEq2385

def B2389 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2389 : B2389.tree = HexagonCover.NBand.M6667_6700.SplitData.node2389 := by
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

def B2388 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2389]
theorem treeEq2388 : B2388.tree = HexagonCover.NBand.M6667_6700.SplitData.node2388 := by
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
  · exact treeEq2389

def B2387 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2388, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2387 : B2387.tree = HexagonCover.NBand.M6667_6700.SplitData.node2387 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2388
  · rfl
  · rfl

def B2383 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2384, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2387]
theorem treeEq2383 : B2383.tree = HexagonCover.NBand.M6667_6700.SplitData.node2383 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2384
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2387

def B2382 : Block := .branch 73 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), B2383, Tip2373_2390, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 1026).pointIds 1026)]
theorem treeEq2382 : B2382.tree = HexagonCover.NBand.M6667_6700.SplitData.node2382 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2383
  · rfl
  · rfl
  · rfl
  · rfl

def B2374 : Block := .branch 72 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B2375, B2382, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq2374 : B2374.tree = HexagonCover.NBand.M6667_6700.SplitData.node2374 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2375
  · exact treeEq2382
  · rfl
  · rfl
  · rfl

def B2373 : Block := .branch 140 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2374, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq2373 : B2373.tree = HexagonCover.NBand.M6667_6700.SplitData.node2373 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2374
  · rfl
  · rfl

theorem accepted2373 : B2373.accepted = true := by decide +kernel
theorem checked2373 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2373 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2373]
  exact B2373.sound accepted2373
#print axioms checked2373

def B2455 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2455 : B2455.tree = HexagonCover.NBand.M6667_6700.SplitData.node2455 := by
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

def B2454 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2455, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2454 : B2454.tree = HexagonCover.NBand.M6667_6700.SplitData.node2454 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2455
  · rfl
  · rfl

def B2453 : Block := .branch 158 ![10636420115946534436330102005306491265, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1199).pointIds 1199), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2454]
theorem treeEq2453 : B2453.tree = HexagonCover.NBand.M6667_6700.SplitData.node2453 := by
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
  · exact treeEq2454

def B2458 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2458 : B2458.tree = HexagonCover.NBand.M6667_6700.SplitData.node2458 := by
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

def B2457 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2458]
theorem treeEq2457 : B2457.tree = HexagonCover.NBand.M6667_6700.SplitData.node2457 := by
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
  · exact treeEq2458

def B2456 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2457, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2456 : B2456.tree = HexagonCover.NBand.M6667_6700.SplitData.node2456 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2457
  · rfl
  · rfl

def B2452 : Block := .branch 123 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2453, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2456]
theorem treeEq2452 : B2452.tree = HexagonCover.NBand.M6667_6700.SplitData.node2452 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2453
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2456

def B2462 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2462 : B2462.tree = HexagonCover.NBand.M6667_6700.SplitData.node2462 := by
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

def B2461 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2462, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2461 : B2461.tree = HexagonCover.NBand.M6667_6700.SplitData.node2461 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2462
  · rfl
  · rfl

def B2460 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2461]
theorem treeEq2460 : B2460.tree = HexagonCover.NBand.M6667_6700.SplitData.node2460 := by
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
  · exact treeEq2461

def B2465 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2465 : B2465.tree = HexagonCover.NBand.M6667_6700.SplitData.node2465 := by
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

def B2464 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2465]
theorem treeEq2464 : B2464.tree = HexagonCover.NBand.M6667_6700.SplitData.node2464 := by
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
  · exact treeEq2465

def B2463 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2464, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2463 : B2463.tree = HexagonCover.NBand.M6667_6700.SplitData.node2463 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2464
  · rfl
  · rfl

def B2459 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2460, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2463]
theorem treeEq2459 : B2459.tree = HexagonCover.NBand.M6667_6700.SplitData.node2459 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2460
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2463

def B2451 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![B2452, B2459, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq2451 : B2451.tree = HexagonCover.NBand.M6667_6700.SplitData.node2451 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2452
  · exact treeEq2459
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2451 : B2451.accepted = true := by decide +kernel
theorem checked2451 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2451 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2451]
  exact B2451.sound accepted2451
#print axioms checked2451

def Tip2450_2451 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2451 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] checked2451
def B2470 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2470 : B2470.tree = HexagonCover.NBand.M6667_6700.SplitData.node2470 := by
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

def B2469 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2470, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2469 : B2469.tree = HexagonCover.NBand.M6667_6700.SplitData.node2469 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2470
  · rfl
  · rfl

def B2468 : Block := .branch 158 ![10636420115946534436330102005306491265, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1199).pointIds 1199), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2469]
theorem treeEq2468 : B2468.tree = HexagonCover.NBand.M6667_6700.SplitData.node2468 := by
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
  · exact treeEq2469

def B2473 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2473 : B2473.tree = HexagonCover.NBand.M6667_6700.SplitData.node2473 := by
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

def B2472 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2473]
theorem treeEq2472 : B2472.tree = HexagonCover.NBand.M6667_6700.SplitData.node2472 := by
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
  · exact treeEq2473

def B2471 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2472, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2471 : B2471.tree = HexagonCover.NBand.M6667_6700.SplitData.node2471 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2472
  · rfl
  · rfl

def B2467 : Block := .branch 123 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2468, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2471]
theorem treeEq2467 : B2467.tree = HexagonCover.NBand.M6667_6700.SplitData.node2467 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2468
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2471

def B2477 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2477 : B2477.tree = HexagonCover.NBand.M6667_6700.SplitData.node2477 := by
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

def B2476 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2477, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2476 : B2476.tree = HexagonCover.NBand.M6667_6700.SplitData.node2476 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2477
  · rfl
  · rfl

def B2475 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2476]
theorem treeEq2475 : B2475.tree = HexagonCover.NBand.M6667_6700.SplitData.node2475 := by
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
  · exact treeEq2476

def B2480 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2480 : B2480.tree = HexagonCover.NBand.M6667_6700.SplitData.node2480 := by
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

def B2479 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2480]
theorem treeEq2479 : B2479.tree = HexagonCover.NBand.M6667_6700.SplitData.node2479 := by
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
  · exact treeEq2480

def B2478 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2479, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2478 : B2478.tree = HexagonCover.NBand.M6667_6700.SplitData.node2478 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2479
  · rfl
  · rfl

def B2474 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2475, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2478]
theorem treeEq2474 : B2474.tree = HexagonCover.NBand.M6667_6700.SplitData.node2474 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2475
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2478

def B2466 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![B2467, B2474, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq2466 : B2466.tree = HexagonCover.NBand.M6667_6700.SplitData.node2466 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2467
  · exact treeEq2474
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2450 : Block := .branch 74 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip2450_2451, B2466, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1027).pointIds 1027)]
theorem treeEq2450 : B2450.tree = HexagonCover.NBand.M6667_6700.SplitData.node2450 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2466
  · rfl
  · rfl
  · rfl

theorem accepted2450 : B2450.accepted = true := by decide +kernel
theorem checked2450 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2450 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2450]
  exact B2450.sound accepted2450
#print axioms checked2450

def Tip2434_2450 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2450 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] checked2450
def B2439 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2439 : B2439.tree = HexagonCover.NBand.M6667_6700.SplitData.node2439 := by
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

def B2438 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2439, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2438 : B2438.tree = HexagonCover.NBand.M6667_6700.SplitData.node2438 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2439
  · rfl
  · rfl

def B2437 : Block := .branch 158 ![10636420115946534436330102005306491265, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1199).pointIds 1199), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2438]
theorem treeEq2437 : B2437.tree = HexagonCover.NBand.M6667_6700.SplitData.node2437 := by
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
  · exact treeEq2438

def B2442 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2442 : B2442.tree = HexagonCover.NBand.M6667_6700.SplitData.node2442 := by
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

def B2441 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2442]
theorem treeEq2441 : B2441.tree = HexagonCover.NBand.M6667_6700.SplitData.node2441 := by
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
  · exact treeEq2442

def B2440 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2441, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2440 : B2440.tree = HexagonCover.NBand.M6667_6700.SplitData.node2440 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2441
  · rfl
  · rfl

def B2436 : Block := .branch 123 ![2596149667207453099645523063734657, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2437, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2440]
theorem treeEq2436 : B2436.tree = HexagonCover.NBand.M6667_6700.SplitData.node2436 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2437
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2440

def B2446 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq2446 : B2446.tree = HexagonCover.NBand.M6667_6700.SplitData.node2446 := by
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

def B2445 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2446, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq2445 : B2445.tree = HexagonCover.NBand.M6667_6700.SplitData.node2445 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2446
  · rfl
  · rfl

def B2444 : Block := .branch 158 ![10636420114708594397044721730407367041, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 1200).pointIds 1200), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2445]
theorem treeEq2444 : B2444.tree = HexagonCover.NBand.M6667_6700.SplitData.node2444 := by
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
  · exact treeEq2445

def B2449 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq2449 : B2449.tree = HexagonCover.NBand.M6667_6700.SplitData.node2449 := by
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

def B2448 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2449]
theorem treeEq2448 : B2448.tree = HexagonCover.NBand.M6667_6700.SplitData.node2448 := by
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
  · exact treeEq2449

def B2447 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2448, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2447 : B2447.tree = HexagonCover.NBand.M6667_6700.SplitData.node2447 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2448
  · rfl
  · rfl

def B2443 : Block := .branch 123 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B2444, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2447]
theorem treeEq2443 : B2443.tree = HexagonCover.NBand.M6667_6700.SplitData.node2443 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2444
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2447

def B2435 : Block := .branch 90 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![B2436, B2443, (.leaf 2 (Common.fact 1194).pointIds 1194), (.leaf 3 (Common.fact 1195).pointIds 1195), (.leaf 4 (Common.fact 1196).pointIds 1196), (.leaf 5 (Common.fact 1197).pointIds 1197), (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq2435 : B2435.tree = HexagonCover.NBand.M6667_6700.SplitData.node2435 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2436
  · exact treeEq2443
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2434 : Block := .branch 73 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), B2435, Tip2434_2450, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 1026).pointIds 1026)]
theorem treeEq2434 : B2434.tree = HexagonCover.NBand.M6667_6700.SplitData.node2434 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2435
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2434 : B2434.accepted = true := by decide +kernel
theorem checked2434 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2434 (maskNeeds ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq2434]
  exact B2434.sound accepted2434
#print axioms checked2434

end HexagonCover.NBand.M6667_6700.SplitTree.Run0032
