import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0027
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1982 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq1982 : B1982.tree = HexagonCover.NBand.M6667_6700.SplitData.node1982 := by
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

def B1981 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1982]
theorem treeEq1981 : B1981.tree = HexagonCover.NBand.M6667_6700.SplitData.node1981 := by
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
  · exact treeEq1982

def B1985 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq1985 : B1985.tree = HexagonCover.NBand.M6667_6700.SplitData.node1985 := by
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

def B1984 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1985]
theorem treeEq1984 : B1984.tree = HexagonCover.NBand.M6667_6700.SplitData.node1984 := by
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
  · exact treeEq1985

def B1983 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1984, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq1983 : B1983.tree = HexagonCover.NBand.M6667_6700.SplitData.node1983 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1984
  · rfl
  · rfl

def B1980 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1981, (.leaf 5 (Common.fact 419).pointIds 419), B1983]
theorem treeEq1980 : B1980.tree = HexagonCover.NBand.M6667_6700.SplitData.node1980 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1981
  · rfl
  · exact treeEq1983

def B1987 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq1987 : B1987.tree = HexagonCover.NBand.M6667_6700.SplitData.node1987 := by
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

def B1986 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1987, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq1986 : B1986.tree = HexagonCover.NBand.M6667_6700.SplitData.node1986 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1987
  · rfl
  · rfl

def B1979 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B1980, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1986]
theorem treeEq1979 : B1979.tree = HexagonCover.NBand.M6667_6700.SplitData.node1979 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1980
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1986

def B1991 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq1991 : B1991.tree = HexagonCover.NBand.M6667_6700.SplitData.node1991 := by
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

def B1990 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1991]
theorem treeEq1990 : B1990.tree = HexagonCover.NBand.M6667_6700.SplitData.node1990 := by
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
  · exact treeEq1991

def B1994 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq1994 : B1994.tree = HexagonCover.NBand.M6667_6700.SplitData.node1994 := by
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

def B1993 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1994]
theorem treeEq1993 : B1993.tree = HexagonCover.NBand.M6667_6700.SplitData.node1993 := by
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
  · exact treeEq1994

def B1992 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B1993, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq1992 : B1992.tree = HexagonCover.NBand.M6667_6700.SplitData.node1992 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1993
  · rfl
  · rfl

def B1989 : Block := .branch 119 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1990, (.leaf 5 (Common.fact 419).pointIds 419), B1992]
theorem treeEq1989 : B1989.tree = HexagonCover.NBand.M6667_6700.SplitData.node1989 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1990
  · rfl
  · exact treeEq1992

def B1996 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq1996 : B1996.tree = HexagonCover.NBand.M6667_6700.SplitData.node1996 := by
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

def B1995 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B1996, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq1995 : B1995.tree = HexagonCover.NBand.M6667_6700.SplitData.node1995 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1996
  · rfl
  · rfl

def B1988 : Block := .branch 112 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B1989, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1995]
theorem treeEq1988 : B1988.tree = HexagonCover.NBand.M6667_6700.SplitData.node1988 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1989
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1995

def B1978 : Block := .branch 72 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B1979, B1988, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq1978 : B1978.tree = HexagonCover.NBand.M6667_6700.SplitData.node1978 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1979
  · exact treeEq1988
  · rfl
  · rfl
  · rfl

def B1977 : Block := .branch 139 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B1978, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq1977 : B1977.tree = HexagonCover.NBand.M6667_6700.SplitData.node1977 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1978
  · rfl
  · rfl

theorem accepted1977 : B1977.accepted = true := by decide +kernel
theorem checked1977 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1977 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664089502943103374982662106317486690926656]) := by
  rw [← treeEq1977]
  exact B1977.sound accepted1977
#print axioms checked1977

def B2020 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2020 : B2020.tree = HexagonCover.NBand.M6667_6700.SplitData.node2020 := by
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

def B2019 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2020, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2019 : B2019.tree = HexagonCover.NBand.M6667_6700.SplitData.node2019 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2020
  · rfl
  · rfl

def B2018 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2019]
theorem treeEq2018 : B2018.tree = HexagonCover.NBand.M6667_6700.SplitData.node2018 := by
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
  · exact treeEq2019

def B2023 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2023 : B2023.tree = HexagonCover.NBand.M6667_6700.SplitData.node2023 := by
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

def B2022 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2023]
theorem treeEq2022 : B2022.tree = HexagonCover.NBand.M6667_6700.SplitData.node2022 := by
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
  · exact treeEq2023

def B2021 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2022, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2021 : B2021.tree = HexagonCover.NBand.M6667_6700.SplitData.node2021 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2022
  · rfl
  · rfl

def B2017 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2018, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2021]
theorem treeEq2017 : B2017.tree = HexagonCover.NBand.M6667_6700.SplitData.node2017 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2018
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2021

def B2027 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2027 : B2027.tree = HexagonCover.NBand.M6667_6700.SplitData.node2027 := by
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

def B2026 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2027, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2026 : B2026.tree = HexagonCover.NBand.M6667_6700.SplitData.node2026 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2027
  · rfl
  · rfl

def B2025 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2026]
theorem treeEq2025 : B2025.tree = HexagonCover.NBand.M6667_6700.SplitData.node2025 := by
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
  · exact treeEq2026

def B2030 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2030 : B2030.tree = HexagonCover.NBand.M6667_6700.SplitData.node2030 := by
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

def B2029 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2030]
theorem treeEq2029 : B2029.tree = HexagonCover.NBand.M6667_6700.SplitData.node2029 := by
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
  · exact treeEq2030

def B2028 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2029, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2028 : B2028.tree = HexagonCover.NBand.M6667_6700.SplitData.node2028 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2029
  · rfl
  · rfl

def B2024 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2025, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2028]
theorem treeEq2024 : B2024.tree = HexagonCover.NBand.M6667_6700.SplitData.node2024 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2025
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2028

def B2016 : Block := .branch 74 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2017, B2024, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2016 : B2016.tree = HexagonCover.NBand.M6667_6700.SplitData.node2016 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2017
  · exact treeEq2024
  · rfl
  · rfl
  · rfl

theorem accepted2016 : B2016.accepted = true := by decide +kernel
theorem checked2016 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2016 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2016]
  exact B2016.sound accepted2016
#print axioms checked2016

def B2051 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2051 : B2051.tree = HexagonCover.NBand.M6667_6700.SplitData.node2051 := by
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

def B2050 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2051, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2050 : B2050.tree = HexagonCover.NBand.M6667_6700.SplitData.node2050 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2051
  · rfl
  · rfl

def B2049 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2050]
theorem treeEq2049 : B2049.tree = HexagonCover.NBand.M6667_6700.SplitData.node2049 := by
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
  · exact treeEq2050

def B2054 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2054 : B2054.tree = HexagonCover.NBand.M6667_6700.SplitData.node2054 := by
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

def B2053 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2054]
theorem treeEq2053 : B2053.tree = HexagonCover.NBand.M6667_6700.SplitData.node2053 := by
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
  · exact treeEq2054

def B2052 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2053, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2052 : B2052.tree = HexagonCover.NBand.M6667_6700.SplitData.node2052 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2053
  · rfl
  · rfl

def B2048 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2049, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2052]
theorem treeEq2048 : B2048.tree = HexagonCover.NBand.M6667_6700.SplitData.node2048 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2049
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2052

def B2058 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2058 : B2058.tree = HexagonCover.NBand.M6667_6700.SplitData.node2058 := by
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

def B2057 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2058, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2057 : B2057.tree = HexagonCover.NBand.M6667_6700.SplitData.node2057 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2058
  · rfl
  · rfl

def B2056 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2057]
theorem treeEq2056 : B2056.tree = HexagonCover.NBand.M6667_6700.SplitData.node2056 := by
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
  · exact treeEq2057

def B2061 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2061 : B2061.tree = HexagonCover.NBand.M6667_6700.SplitData.node2061 := by
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

def B2060 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2061]
theorem treeEq2060 : B2060.tree = HexagonCover.NBand.M6667_6700.SplitData.node2060 := by
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
  · exact treeEq2061

def B2059 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2060, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2059 : B2059.tree = HexagonCover.NBand.M6667_6700.SplitData.node2059 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2060
  · rfl
  · rfl

def B2055 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2056, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2059]
theorem treeEq2055 : B2055.tree = HexagonCover.NBand.M6667_6700.SplitData.node2055 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2056
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2059

def B2047 : Block := .branch 74 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2048, B2055, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2047 : B2047.tree = HexagonCover.NBand.M6667_6700.SplitData.node2047 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2048
  · exact treeEq2055
  · rfl
  · rfl
  · rfl

theorem accepted2047 : B2047.accepted = true := by decide +kernel
theorem checked2047 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2047 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2047]
  exact B2047.sound accepted2047
#print axioms checked2047

def Tip2015_2016 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2016 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] checked2016
def B2035 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2035 : B2035.tree = HexagonCover.NBand.M6667_6700.SplitData.node2035 := by
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

def B2034 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2035, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2034 : B2034.tree = HexagonCover.NBand.M6667_6700.SplitData.node2034 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2035
  · rfl
  · rfl

def B2033 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2034]
theorem treeEq2033 : B2033.tree = HexagonCover.NBand.M6667_6700.SplitData.node2033 := by
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
  · exact treeEq2034

def B2038 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2038 : B2038.tree = HexagonCover.NBand.M6667_6700.SplitData.node2038 := by
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

def B2037 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2038]
theorem treeEq2037 : B2037.tree = HexagonCover.NBand.M6667_6700.SplitData.node2037 := by
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
  · exact treeEq2038

def B2036 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2037, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2036 : B2036.tree = HexagonCover.NBand.M6667_6700.SplitData.node2036 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2037
  · rfl
  · rfl

def B2032 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2033, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2036]
theorem treeEq2032 : B2032.tree = HexagonCover.NBand.M6667_6700.SplitData.node2032 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2033
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2036

def B2042 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2042 : B2042.tree = HexagonCover.NBand.M6667_6700.SplitData.node2042 := by
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

def B2041 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), B2042, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2041 : B2041.tree = HexagonCover.NBand.M6667_6700.SplitData.node2041 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2042
  · rfl
  · rfl

def B2040 : Block := .branch 158 ![10636420114709198859954529044994720129, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2041]
theorem treeEq2040 : B2040.tree = HexagonCover.NBand.M6667_6700.SplitData.node2040 := by
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
  · exact treeEq2041

def B2045 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2045 : B2045.tree = HexagonCover.NBand.M6667_6700.SplitData.node2045 := by
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

def B2044 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2045]
theorem treeEq2044 : B2044.tree = HexagonCover.NBand.M6667_6700.SplitData.node2044 := by
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
  · exact treeEq2045

def B2043 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2044, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2043 : B2043.tree = HexagonCover.NBand.M6667_6700.SplitData.node2043 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2044
  · rfl
  · rfl

def B2039 : Block := .branch 123 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2040, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2043]
theorem treeEq2039 : B2039.tree = HexagonCover.NBand.M6667_6700.SplitData.node2039 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2040
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2043

def B2031 : Block := .branch 74 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2032, B2039, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2031 : B2031.tree = HexagonCover.NBand.M6667_6700.SplitData.node2031 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2032
  · exact treeEq2039
  · rfl
  · rfl
  · rfl

def B2015 : Block := .branch 73 ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 916).pointIds 916), (.leaf 1 (Common.fact 917).pointIds 917), Tip2015_2016, B2031, (.leaf 4 (Common.fact 918).pointIds 918), (.leaf 5 (Common.fact 919).pointIds 919), (.leaf 6 (Common.fact 939).pointIds 939)]
theorem treeEq2015 : B2015.tree = HexagonCover.NBand.M6667_6700.SplitData.node2015 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2031
  · rfl
  · rfl
  · rfl

theorem accepted2015 : B2015.accepted = true := by decide +kernel
theorem checked2015 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2015 (maskNeeds ![2596148429871876724072562751963521, 1297037792194332162, 9007199254747140, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2015]
  exact B2015.sound accepted2015
#print axioms checked2015

end HexagonCover.NBand.M6667_6700.SplitTree.Run0027
