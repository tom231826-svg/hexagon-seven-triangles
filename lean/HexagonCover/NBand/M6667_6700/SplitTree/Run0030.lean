import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0026
import HexagonCover.NBand.M6667_6700.SplitTree.Run0027
import HexagonCover.NBand.M6667_6700.SplitTree.Run0028
import HexagonCover.NBand.M6667_6700.SplitTree.Run0029
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0030
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B2225 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq2225 : B2225.tree = HexagonCover.NBand.M6667_6700.SplitData.node2225 := by
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

def B2224 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2225]
theorem treeEq2224 : B2224.tree = HexagonCover.NBand.M6667_6700.SplitData.node2224 := by
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
  · exact treeEq2225

def B2228 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2228 : B2228.tree = HexagonCover.NBand.M6667_6700.SplitData.node2228 := by
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

def B2227 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2228]
theorem treeEq2227 : B2227.tree = HexagonCover.NBand.M6667_6700.SplitData.node2227 := by
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
  · exact treeEq2228

def B2226 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2227, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq2226 : B2226.tree = HexagonCover.NBand.M6667_6700.SplitData.node2226 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2227
  · rfl
  · rfl

def B2223 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2224, (.leaf 5 (Common.fact 419).pointIds 419), B2226]
theorem treeEq2223 : B2223.tree = HexagonCover.NBand.M6667_6700.SplitData.node2223 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2224
  · rfl
  · exact treeEq2226

def B2230 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq2230 : B2230.tree = HexagonCover.NBand.M6667_6700.SplitData.node2230 := by
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

def B2229 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2230, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq2229 : B2229.tree = HexagonCover.NBand.M6667_6700.SplitData.node2229 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2230
  · rfl
  · rfl

def B2222 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B2223, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2229]
theorem treeEq2222 : B2222.tree = HexagonCover.NBand.M6667_6700.SplitData.node2222 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2223
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2229

def B2234 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq2234 : B2234.tree = HexagonCover.NBand.M6667_6700.SplitData.node2234 := by
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

def B2233 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2234]
theorem treeEq2233 : B2233.tree = HexagonCover.NBand.M6667_6700.SplitData.node2233 := by
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
  · exact treeEq2234

def B2237 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2237 : B2237.tree = HexagonCover.NBand.M6667_6700.SplitData.node2237 := by
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

def B2236 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2237]
theorem treeEq2236 : B2236.tree = HexagonCover.NBand.M6667_6700.SplitData.node2236 := by
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
  · exact treeEq2237

def B2235 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2236, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq2235 : B2235.tree = HexagonCover.NBand.M6667_6700.SplitData.node2235 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2236
  · rfl
  · rfl

def B2232 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2233, (.leaf 5 (Common.fact 419).pointIds 419), B2235]
theorem treeEq2232 : B2232.tree = HexagonCover.NBand.M6667_6700.SplitData.node2232 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2233
  · rfl
  · exact treeEq2235

def B2239 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq2239 : B2239.tree = HexagonCover.NBand.M6667_6700.SplitData.node2239 := by
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

def B2238 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2239, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq2238 : B2238.tree = HexagonCover.NBand.M6667_6700.SplitData.node2238 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2239
  · rfl
  · rfl

def B2231 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B2232, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B2238]
theorem treeEq2231 : B2231.tree = HexagonCover.NBand.M6667_6700.SplitData.node2231 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2232
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2238

def B2221 : Block := .branch 72 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B2222, B2231, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq2221 : B2221.tree = HexagonCover.NBand.M6667_6700.SplitData.node2221 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2222
  · exact treeEq2231
  · rfl
  · rfl
  · rfl

def B2220 : Block := .branch 139 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B2221, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq2220 : B2220.tree = HexagonCover.NBand.M6667_6700.SplitData.node2220 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2221
  · rfl
  · rfl

theorem accepted2220 : B2220.accepted = true := by decide +kernel
theorem checked2220 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2220 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656]) := by
  rw [← treeEq2220]
  exact B2220.sound accepted2220
#print axioms checked2220

def Tip1997_2014 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2014 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0028.checked2014
def Tip1997_2077 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2077 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] HexagonCover.NBand.M6667_6700.SplitTree.Run0029.checked2077
def Tip1997_2220 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2220 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] checked2220
def B2000 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2000 : B2000.tree = HexagonCover.NBand.M6667_6700.SplitData.node2000 := by
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

def B1999 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2000]
theorem treeEq1999 : B1999.tree = HexagonCover.NBand.M6667_6700.SplitData.node1999 := by
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
  · exact treeEq2000

def B2005 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2005 : B2005.tree = HexagonCover.NBand.M6667_6700.SplitData.node2005 := by
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

def B2004 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B2005]
theorem treeEq2004 : B2004.tree = HexagonCover.NBand.M6667_6700.SplitData.node2004 := by
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
  · exact treeEq2005

def B2008 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2008 : B2008.tree = HexagonCover.NBand.M6667_6700.SplitData.node2008 := by
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

def B2007 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2008]
theorem treeEq2007 : B2007.tree = HexagonCover.NBand.M6667_6700.SplitData.node2007 := by
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
  · exact treeEq2008

def B2013 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2013 : B2013.tree = HexagonCover.NBand.M6667_6700.SplitData.node2013 := by
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

def B2012 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2013, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2012 : B2012.tree = HexagonCover.NBand.M6667_6700.SplitData.node2012 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2013
  · rfl
  · rfl

def B2011 : Block := .branch 158 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1190).pointIds 1190), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2012]
theorem treeEq2011 : B2011.tree = HexagonCover.NBand.M6667_6700.SplitData.node2011 := by
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
  · exact treeEq2012

def B2010 : Block := .branch 163 ![5316911983140267954525035555708731777, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1189).pointIds 1189), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2011]
theorem treeEq2010 : B2010.tree = HexagonCover.NBand.M6667_6700.SplitData.node2010 := by
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
  · exact treeEq2011

def B2009 : Block := .branch 122 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B2010, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip1997_2014]
theorem treeEq2009 : B2009.tree = HexagonCover.NBand.M6667_6700.SplitData.node2009 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2006 : Block := .branch 121 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2007, (.leaf 5 (Common.fact 430).pointIds 430), B2009]
theorem treeEq2006 : B2006.tree = HexagonCover.NBand.M6667_6700.SplitData.node2006 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2007
  · rfl
  · exact treeEq2009

def B2003 : Block := .branch 120 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2004, (.leaf 5 (Common.fact 163).pointIds 163), B2006]
theorem treeEq2003 : B2003.tree = HexagonCover.NBand.M6667_6700.SplitData.node2003 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2004
  · rfl
  · exact treeEq2006

def B2002 : Block := .branch 79 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![B2003, Tip1997_2077, (.leaf 2 (Common.fact 1184).pointIds 1184), (.leaf 3 (Common.fact 1185).pointIds 1185), (.leaf 4 (Common.fact 1186).pointIds 1186), (.leaf 5 (Common.fact 1187).pointIds 1187), (.leaf 6 (Common.fact 1201).pointIds 1201)]
theorem treeEq2002 : B2002.tree = HexagonCover.NBand.M6667_6700.SplitData.node2002 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2003
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2001 : Block := .branch 140 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2002, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2001 : B2001.tree = HexagonCover.NBand.M6667_6700.SplitData.node2001 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2002
  · rfl
  · rfl

def B1998 : Block := .branch 119 ![2596148429267413814265248164610433, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1999, (.leaf 5 (Common.fact 419).pointIds 419), B2001]
theorem treeEq1998 : B1998.tree = HexagonCover.NBand.M6667_6700.SplitData.node1998 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1999
  · rfl
  · exact treeEq2001

def B1997 : Block := .branch 111 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B1998, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip1997_2220]
theorem treeEq1997 : B1997.tree = HexagonCover.NBand.M6667_6700.SplitData.node1997 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1998
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1997 : B1997.accepted = true := by decide +kernel
theorem checked1997 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1997 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320]) := by
  rw [← treeEq1997]
  exact B1997.sound accepted1997
#print axioms checked1997

def Tip1894_1914 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1914 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] HexagonCover.NBand.M6667_6700.SplitTree.Run0026.checked1914
def Tip1894_1977 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1977 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] HexagonCover.NBand.M6667_6700.SplitTree.Run0027.checked1977
def Tip1894_1997 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1997 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] checked1997
def B1896 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq1896 : B1896.tree = HexagonCover.NBand.M6667_6700.SplitData.node1896 := by
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

def B1895 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B1896]
theorem treeEq1895 : B1895.tree = HexagonCover.NBand.M6667_6700.SplitData.node1895 := by
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
  · exact treeEq1896

def B1901 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405366099312816824339923008] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1901 : B1901.tree = HexagonCover.NBand.M6667_6700.SplitData.node1901 := by
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

def B1900 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588771015362406752986877919296] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1901]
theorem treeEq1900 : B1900.tree = HexagonCover.NBand.M6667_6700.SplitData.node1900 := by
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
  · exact treeEq1901

def B1905 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393797904136159731261855295847582874566672, 393248, 7108743963977512458757354744165609037937198459519040] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 906).pointIds 906), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq1905 : B1905.tree = HexagonCover.NBand.M6667_6700.SplitData.node1905 := by
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

def B1904 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1393797904136159731261855295847582874566672, 393248, 6360455125664090164637068109814872131873360997515328] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 905).pointIds 905), (.leaf 5 (Common.fact 371).pointIds 371), B1905]
theorem treeEq1904 : B1904.tree = HexagonCover.NBand.M6667_6700.SplitData.node1904 := by
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
  · exact treeEq1905

def B1908 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754309463115164865068007488] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq1908 : B1908.tree = HexagonCover.NBand.M6667_6700.SplitData.node1908 := by
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

def B1907 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216906515490909515219992640] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B1908]
theorem treeEq1907 : B1907.tree = HexagonCover.NBand.M6667_6700.SplitData.node1907 := by
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
  · exact treeEq1908

def B1913 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq1913 : B1913.tree = HexagonCover.NBand.M6667_6700.SplitData.node1913 := by
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

def B1912 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254216413159698894650081344] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1913, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq1912 : B1912.tree = HexagonCover.NBand.M6667_6700.SplitData.node1912 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1913
  · rfl
  · rfl

def B1911 : Block := .branch 158 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055333008234088943980666945600] ![(.leaf 0 (Common.fact 1181).pointIds 1181), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1912]
theorem treeEq1911 : B1911.tree = HexagonCover.NBand.M6667_6700.SplitData.node1911 := by
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
  · exact treeEq1912

def B1910 : Block := .branch 163 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823092425854346503824786733206601792] ![(.leaf 0 (Common.fact 1180).pointIds 1180), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B1911]
theorem treeEq1910 : B1910.tree = HexagonCover.NBand.M6667_6700.SplitData.node1910 := by
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
  · exact treeEq1911

def B1909 : Block := .branch 122 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664092823093059679646617939487481558204480] ![B1910, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip1894_1914]
theorem treeEq1909 : B1909.tree = HexagonCover.NBand.M6667_6700.SplitData.node1909 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1910
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1906 : Block := .branch 121 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664091495163138109364451942813045360164928] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B1907, (.leaf 5 (Common.fact 430).pointIds 430), B1909]
theorem treeEq1906 : B1906.tree = HexagonCover.NBand.M6667_6700.SplitData.node1906 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1907
  · rfl
  · exact treeEq1909

def B1903 : Block := .branch 120 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B1904, (.leaf 5 (Common.fact 163).pointIds 163), B1906]
theorem treeEq1903 : B1903.tree = HexagonCover.NBand.M6667_6700.SplitData.node1903 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1904
  · rfl
  · exact treeEq1906

def B1902 : Block := .branch 140 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090165935142324448579039005985079820352] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1903, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq1902 : B1902.tree = HexagonCover.NBand.M6667_6700.SplitData.node1902 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1903
  · rfl
  · rfl

def B1899 : Block := .branch 119 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1900, (.leaf 5 (Common.fact 419).pointIds 419), B1902]
theorem treeEq1899 : B1899.tree = HexagonCover.NBand.M6667_6700.SplitData.node1899 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1900
  · rfl
  · exact treeEq1902

def B1898 : Block := .branch 111 ![590295810358705652097, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B1899, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip1894_1977]
theorem treeEq1898 : B1898.tree = HexagonCover.NBand.M6667_6700.SplitData.node1898 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1899
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1897 : Block := .branch 69 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501645662985649069313885610960224320] ![B1898, Tip1894_1997, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1897 : B1897.tree = HexagonCover.NBand.M6667_6700.SplitData.node1897 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1898
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1894 : Block := .branch 108 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B1895, (.leaf 5 (Common.fact 136).pointIds 136), B1897]
theorem treeEq1894 : B1894.tree = HexagonCover.NBand.M6667_6700.SplitData.node1894 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1895
  · rfl
  · exact treeEq1897

theorem accepted1894 : B1894.accepted = true := by decide +kernel
theorem checked1894 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1894 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq1894]
  exact B1894.sound accepted1894
#print axioms checked1894

def Tip1889_1894 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1894 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089501321461344640699644452829115449408] checked1894
def B2242 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq2242 : B2242.tree = HexagonCover.NBand.M6667_6700.SplitData.node2242 := by
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

def B2241 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2242]
theorem treeEq2241 : B2241.tree = HexagonCover.NBand.M6667_6700.SplitData.node2241 := by
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
  · exact treeEq2242

def B2240 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2241, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq2240 : B2240.tree = HexagonCover.NBand.M6667_6700.SplitData.node2240 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2241
  · rfl
  · rfl

def B1893 : Block := .branch 101 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![Tip1889_1894, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B2240]
theorem treeEq1893 : B1893.tree = HexagonCover.NBand.M6667_6700.SplitData.node1893 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2240

def B2245 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq2245 : B2245.tree = HexagonCover.NBand.M6667_6700.SplitData.node2245 := by
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

def B2244 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2245]
theorem treeEq2244 : B2244.tree = HexagonCover.NBand.M6667_6700.SplitData.node2244 := by
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
  · exact treeEq2245

def B2243 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2244, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq2243 : B2243.tree = HexagonCover.NBand.M6667_6700.SplitData.node2243 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2244
  · rfl
  · rfl

def B1892 : Block := .branch 91 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![B1893, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B2243]
theorem treeEq1892 : B1892.tree = HexagonCover.NBand.M6667_6700.SplitData.node1892 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1893
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2243

def B2248 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq2248 : B2248.tree = HexagonCover.NBand.M6667_6700.SplitData.node2248 := by
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

def B2247 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2248]
theorem treeEq2247 : B2247.tree = HexagonCover.NBand.M6667_6700.SplitData.node2247 := by
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
  · exact treeEq2248

def B2246 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2247, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq2246 : B2246.tree = HexagonCover.NBand.M6667_6700.SplitData.node2246 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2247
  · rfl
  · rfl

def B1891 : Block := .branch 89 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B1892, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B2246]
theorem treeEq1891 : B1891.tree = HexagonCover.NBand.M6667_6700.SplitData.node1891 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1892
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2246

def B2251 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq2251 : B2251.tree = HexagonCover.NBand.M6667_6700.SplitData.node2251 := by
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

def B2250 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2251]
theorem treeEq2250 : B2250.tree = HexagonCover.NBand.M6667_6700.SplitData.node2250 := by
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
  · exact treeEq2251

def B2249 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2250, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq2249 : B2249.tree = HexagonCover.NBand.M6667_6700.SplitData.node2249 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2250
  · rfl
  · rfl

def B1890 : Block := .branch 86 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B1891, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B2249]
theorem treeEq1890 : B1890.tree = HexagonCover.NBand.M6667_6700.SplitData.node1890 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1891
  · rfl
  · rfl
  · exact treeEq2249

def B2254 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq2254 : B2254.tree = HexagonCover.NBand.M6667_6700.SplitData.node2254 := by
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

def B2253 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2254]
theorem treeEq2253 : B2253.tree = HexagonCover.NBand.M6667_6700.SplitData.node2253 := by
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
  · exact treeEq2254

def B2252 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2253, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq2252 : B2252.tree = HexagonCover.NBand.M6667_6700.SplitData.node2252 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2253
  · rfl
  · rfl

def B1889 : Block := .branch 85 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B1890, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B2252]
theorem treeEq1889 : B1889.tree = HexagonCover.NBand.M6667_6700.SplitData.node1889 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1890
  · rfl
  · rfl
  · exact treeEq2252

theorem accepted1889 : B1889.accepted = true := by decide +kernel
theorem checked1889 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1889 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq1889]
  exact B1889.sound accepted1889
#print axioms checked1889

end HexagonCover.NBand.M6667_6700.SplitTree.Run0030
