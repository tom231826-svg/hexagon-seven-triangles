import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0016
import HexagonCover.NBand.M8300_8500.SplitTree.Run0022
import HexagonCover.NBand.M8300_8500.SplitTree.Run0027
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0028
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip1237_1238 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1238 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0022.checked1238
def B1656 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq1656 : B1656.tree = HexagonCover.NBand.M8300_8500.SplitData.node1656 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1655 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1656, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq1655 : B1655.tree = HexagonCover.NBand.M8300_8500.SplitData.node1655 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1656
  · rfl

def B1654 : Block := .branch 84 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B1655, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1654 : B1654.tree = HexagonCover.NBand.M8300_8500.SplitData.node1654 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1655
  · rfl
  · rfl
  · rfl
  · rfl

def B1653 : Block := .branch 85 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B1654, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq1653 : B1653.tree = HexagonCover.NBand.M8300_8500.SplitData.node1653 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1654
  · rfl
  · rfl
  · rfl
  · rfl

def B1652 : Block := .branch 86 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B1653, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1652 : B1652.tree = HexagonCover.NBand.M8300_8500.SplitData.node1652 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1653
  · rfl
  · rfl
  · rfl
  · rfl

def B1651 : Block := .branch 129 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B1652, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1651 : B1651.tree = HexagonCover.NBand.M8300_8500.SplitData.node1651 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1652
  · rfl
  · rfl

def B1650 : Block := .branch 138 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B1651, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1650 : B1650.tree = HexagonCover.NBand.M8300_8500.SplitData.node1650 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1651
  · rfl
  · rfl

def B1649 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1650, (.leaf 0 [] 0)]
theorem treeEq1649 : B1649.tree = HexagonCover.NBand.M8300_8500.SplitData.node1649 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1650
  · rfl

def B1648 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1649, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1648 : B1648.tree = HexagonCover.NBand.M8300_8500.SplitData.node1648 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1649
  · rfl

def B1647 : Block := .branch 146 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B1648, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1647 : B1647.tree = HexagonCover.NBand.M8300_8500.SplitData.node1647 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1648
  · rfl
  · rfl

def B1646 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B1647, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1646 : B1646.tree = HexagonCover.NBand.M8300_8500.SplitData.node1646 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1647
  · rfl
  · rfl
  · rfl

def B1645 : Block := .branch 161 ![604463488519866704462209, 151152620940525821756930, 113336795588871485134852, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 900).pointIds 900), (.leaf 3 (Common.fact 901).pointIds 901), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B1646]
theorem treeEq1645 : B1645.tree = HexagonCover.NBand.M8300_8500.SplitData.node1645 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1646

def B1237 : Block := .branch 76 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip1237_1238, B1645, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1237 : B1237.tree = HexagonCover.NBand.M8300_8500.SplitData.node1237 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1645
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1237 : B1237.accepted = true := by decide +kernel
theorem checked1237 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1237 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1237]
  exact B1237.sound accepted1237
#print axioms checked1237

def Tip1230_1658 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1658 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0027.checked1658
def Tip1230_1237 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1237 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1237
def B2076 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), (.leaf 6 (Common.fact 905).pointIds 905)]
theorem treeEq2076 : B2076.tree = HexagonCover.NBand.M8300_8500.SplitData.node2076 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2075 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786835434728643008795011607779651310952382528] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2076, (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2075 : B2075.tree = HexagonCover.NBand.M8300_8500.SplitData.node2075 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2076
  · rfl

def B2074 : Block := .branch 84 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B2075, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2074 : B2074.tree = HexagonCover.NBand.M8300_8500.SplitData.node2074 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2075
  · rfl
  · rfl
  · rfl
  · rfl

def B2073 : Block := .branch 85 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B2074, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq2073 : B2073.tree = HexagonCover.NBand.M8300_8500.SplitData.node2073 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2074
  · rfl
  · rfl
  · rfl
  · rfl

def B2072 : Block := .branch 86 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B2073, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2072 : B2072.tree = HexagonCover.NBand.M8300_8500.SplitData.node2072 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2073
  · rfl
  · rfl
  · rfl
  · rfl

def B2071 : Block := .branch 129 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857218117037931996336755369755185239294016] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B2072, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2071 : B2071.tree = HexagonCover.NBand.M8300_8500.SplitData.node2071 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2072
  · rfl
  · rfl

def B2070 : Block := .branch 138 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B2071, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2070 : B2070.tree = HexagonCover.NBand.M8300_8500.SplitData.node2070 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2071
  · rfl
  · rfl

def B2069 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2070, (.leaf 0 [] 0)]
theorem treeEq2069 : B2069.tree = HexagonCover.NBand.M8300_8500.SplitData.node2069 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2070
  · rfl

def B2068 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2069, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2068 : B2068.tree = HexagonCover.NBand.M8300_8500.SplitData.node2068 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2069
  · rfl

def B2067 : Block := .branch 146 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B2068, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2067 : B2067.tree = HexagonCover.NBand.M8300_8500.SplitData.node2067 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2068
  · rfl
  · rfl

def B2066 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3370222786857239384685864554990721830668149724807232] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B2067, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq2066 : B2066.tree = HexagonCover.NBand.M8300_8500.SplitData.node2066 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2067
  · rfl
  · rfl
  · rfl

def B2065 : Block := .branch 161 ![604463488519866704462209, 151152620940525821756930, 113336795588871485134852, 79232998217542796110242799624, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 900).pointIds 900), (.leaf 3 (Common.fact 901).pointIds 901), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B2066]
theorem treeEq2065 : B2065.tree = HexagonCover.NBand.M8300_8500.SplitData.node2065 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2066

def B1657 : Block := .branch 76 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip1230_1658, B2065, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1657 : B1657.tree = HexagonCover.NBand.M8300_8500.SplitData.node1657 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2065
  · rfl
  · rfl
  · rfl
  · rfl

def B1236 : Block := .branch 68 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1230_1237, B1657, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M8300_8500.SplitData.node1236 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1657
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1235 : Block := .branch 109 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163153149078631728573227414642065424, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B1236, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M8300_8500.SplitData.node1235 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1236
  · rfl
  · rfl

def B1234 : Block := .branch 171 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 869).pointIds 869), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B1235]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M8300_8500.SplitData.node1234 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1235

def B1233 : Block := .branch 97 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B1234, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M8300_8500.SplitData.node1233 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1234
  · rfl
  · rfl
  · rfl

def B1232 : Block := .branch 107 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B1233, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M8300_8500.SplitData.node1232 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1233
  · rfl
  · rfl
  · rfl

def B1231 : Block := .branch 118 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B1232, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M8300_8500.SplitData.node1231 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1232
  · rfl
  · rfl
  · rfl

def B1230 : Block := .branch 128 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B1231, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M8300_8500.SplitData.node1230 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1231
  · rfl
  · rfl
  · rfl

theorem accepted1230 : B1230.accepted = true := by decide +kernel
theorem checked1230 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1230 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq1230]
  exact B1230.sound accepted1230
#print axioms checked1230

def B2096 : Block := .branch 168 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 158456325028528675187087925256, 2854500831259018492916903225796516241337319440, 5709034369502101269473775122669557740833472544, 11172171938396184191687944481920642746679360] ![(.leaf 0 (Common.fact 923).pointIds 923), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 924).pointIds 924), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq2096 : B2096.tree = HexagonCover.NBand.M8300_8500.SplitData.node2096 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2095 : Block := .branch 120 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 158456325028528675187087925256, 2854500829929790497131987352892709181056974864, 5709034369502101269473775122669557740833472544, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B2096, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 922).pointIds 922)]
theorem treeEq2095 : B2095.tree = HexagonCover.NBand.M8300_8500.SplitData.node2095 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2096
  · rfl
  · rfl

def B2094 : Block := .branch 125 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 158456325028528675187087925256, 2854500829929790497131987352892709181056974864, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B2095, (.leaf 6 (Common.fact 921).pointIds 921)]
theorem treeEq2094 : B2094.tree = HexagonCover.NBand.M8300_8500.SplitData.node2094 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2095
  · rfl

def B2093 : Block := .branch 130 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81327708820892342539772865044488, 2854500829929790497131987352892709181056974864, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), B2094, (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2093 : B2093.tree = HexagonCover.NBand.M8300_8500.SplitData.node2093 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2094
  · rfl
  · rfl

def B2092 : Block := .branch 131 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81327708820892342539772865044488, 2854500829929790497131987352892709181056974864, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), B2093, (.leaf 5 (Common.fact 733).pointIds 733), (.leaf 6 (Common.fact 919).pointIds 919)]
theorem treeEq2092 : B2092.tree = HexagonCover.NBand.M8300_8500.SplitData.node2092 := by
  change Tree.branch (131 : Fin 177) _ = Tree.branch (131 : Fin 177) _
  apply congrArg (Tree.branch (131 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2093
  · rfl
  · rfl

def B2091 : Block := .branch 132 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81327708820892342539772865044488, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B2092, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 918).pointIds 918)]
theorem treeEq2091 : B2091.tree = HexagonCover.NBand.M8300_8500.SplitData.node2091 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2092
  · rfl
  · rfl

def B2090 : Block := .branch 139 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81327708820892342539772865044488, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B2091, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 917).pointIds 917)]
theorem treeEq2090 : B2090.tree = HexagonCover.NBand.M8300_8500.SplitData.node2090 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2091
  · rfl
  · rfl

def B2089 : Block := .branch 140 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81327708820892342539772865044488, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B2090, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 916).pointIds 916)]
theorem treeEq2089 : B2089.tree = HexagonCover.NBand.M8300_8500.SplitData.node2089 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2090
  · rfl
  · rfl

def B2088 : Block := .branch 97 ![10384593717069655835773544775549313, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B2089, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 915).pointIds 915)]
theorem treeEq2088 : B2088.tree = HexagonCover.NBand.M8300_8500.SplitData.node2088 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2089
  · rfl
  · rfl
  · rfl

def B2087 : Block := .branch 113 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2854495385411919762116571938898990272765591568, 5709034326966805404356467189747731811862446112, 11172177255308167331351436097148883868057664] ![B2088, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), (.leaf 6 (Common.fact 914).pointIds 914)]
theorem treeEq2087 : B2087.tree = HexagonCover.NBand.M8300_8500.SplitData.node2087 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2088
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2086 : Block := .branch 135 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2854495385411919762116571938898990272765591568, 5708990770823839524233143877797980545531379744, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2087, (.leaf 6 (Common.fact 913).pointIds 913)]
theorem treeEq2086 : B2086.tree = HexagonCover.NBand.M8300_8500.SplitData.node2086 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2087
  · rfl

def B2085 : Block := .branch 144 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2854495385411919762116571938898990272765591568, 5708990770823839524233143877797980545531379744, 11172177255308167331351436097148883868057664] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B2086, (.leaf 6 (Common.fact 912).pointIds 912)]
theorem treeEq2085 : B2085.tree = HexagonCover.NBand.M8300_8500.SplitData.node2085 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2086
  · rfl

def B2084 : Block := .branch 143 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2862858164861368745794647833251233408330334224, 5708990770823839524233143877797980545531379744, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 911).pointIds 911), (.leaf 5 (Common.fact 217).pointIds 217), B2085]
theorem treeEq2084 : B2084.tree = HexagonCover.NBand.M8300_8500.SplitData.node2084 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2085

def B2083 : Block := .branch 141 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2860070571711552417901955868467152363142086672, 5708990770823839524233143877797980545531379744, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), B2084, (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 910).pointIds 910)]
theorem treeEq2083 : B2083.tree = HexagonCover.NBand.M8300_8500.SplitData.node2083 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2084
  · rfl
  · rfl

def B2082 : Block := .branch 152 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2860070571711552417901955868467152363142086672, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 908).pointIds 908), B2083, (.leaf 6 (Common.fact 909).pointIds 909)]
theorem treeEq2082 : B2082.tree = HexagonCover.NBand.M8300_8500.SplitData.node2082 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2083
  · rfl

def B2081 : Block := .branch 142 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 2854495385411919762116571938898990272765591568, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B2082, (.leaf 5 (Common.fact 286).pointIds 286), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2081 : B2081.tree = HexagonCover.NBand.M8300_8500.SplitData.node2081 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2082
  · rfl
  · rfl

def B2080 : Block := .branch 107 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2081, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2080 : B2080.tree = HexagonCover.NBand.M8300_8500.SplitData.node2080 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2081
  · rfl
  · rfl
  · rfl

def B2079 : Block := .branch 118 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B2080, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq2079 : B2079.tree = HexagonCover.NBand.M8300_8500.SplitData.node2079 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2080
  · rfl
  · rfl
  · rfl

def B2078 : Block := .branch 128 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 3032901347000164747248857685080177164813434896, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B2079, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq2078 : B2078.tree = HexagonCover.NBand.M8300_8500.SplitData.node2078 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2079
  · rfl
  · rfl
  · rfl

def B2077 : Block := .branch 151 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855760583576960824703115067456] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B2078, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 906).pointIds 906)]
theorem treeEq2077 : B2077.tree = HexagonCover.NBand.M8300_8500.SplitData.node2077 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2078
  · rfl
  · rfl

theorem accepted2077 : B2077.accepted = true := by decide +kernel
theorem checked2077 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2077 (maskNeeds ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855760583576960824703115067456]) := by
  rw [← treeEq2077]
  exact B2077.sound accepted2077
#print axioms checked2077

def Tip0030_0906 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0906 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0016.checked0906
def Tip0030_0033 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0033 ![604463488519866704462209, 151152765055713897612802, 14544888767238507258189828, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0016.checked0033
def Tip0030_1230 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1230 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] checked1230
def Tip0030_2077 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2077 ![578712552117109121, 151152620940525821756930, 37778931862957161715716, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855760583576960824703115067456] checked2077
def B0905 : Block := .branch 109 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163153149078631728573227414642065424, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), Tip0030_0906, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0905 : B0905.tree = HexagonCover.NBand.M8300_8500.SplitData.node0905 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0904 : Block := .branch 171 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B0905]
theorem treeEq0904 : B0904.tree = HexagonCover.NBand.M8300_8500.SplitData.node0904 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0905

def B0903 : Block := .branch 97 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B0904, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq0903 : B0903.tree = HexagonCover.NBand.M8300_8500.SplitData.node0903 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0904
  · rfl
  · rfl
  · rfl

def B0902 : Block := .branch 107 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B0903, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0902 : B0902.tree = HexagonCover.NBand.M8300_8500.SplitData.node0902 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0903
  · rfl
  · rfl
  · rfl

def B0901 : Block := .branch 118 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B0902, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq0901 : B0901.tree = HexagonCover.NBand.M8300_8500.SplitData.node0901 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0902
  · rfl
  · rfl
  · rfl

def B0900 : Block := .branch 128 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B0901, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq0900 : B0900.tree = HexagonCover.NBand.M8300_8500.SplitData.node0900 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0901
  · rfl
  · rfl
  · rfl

def B0899 : Block := .branch 120 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0900, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0899 : B0899.tree = HexagonCover.NBand.M8300_8500.SplitData.node0899 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0900
  · rfl
  · rfl

def B0898 : Block := .branch 143 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B0899]
theorem treeEq0898 : B0898.tree = HexagonCover.NBand.M8300_8500.SplitData.node0898 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0899

def B0897 : Block := .branch 140 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B0898, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0897 : B0897.tree = HexagonCover.NBand.M8300_8500.SplitData.node0897 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0898
  · rfl
  · rfl

def B0896 : Block := .branch 148 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B0897, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0896 : B0896.tree = HexagonCover.NBand.M8300_8500.SplitData.node0896 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0897
  · rfl
  · rfl

def B0895 : Block := .branch 168 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 837).pointIds 837), (.leaf 3 (Common.fact 838).pointIds 838), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B0896]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M8300_8500.SplitData.node0895 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0896

def B0032 : Block := .branch 83 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip0030_0033, B0895, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M8300_8500.SplitData.node0032 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0895
  · rfl
  · rfl
  · rfl

def B1229 : Block := .branch 120 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), Tip0030_1230, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M8300_8500.SplitData.node1229 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1228 : Block := .branch 143 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B1229]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M8300_8500.SplitData.node1228 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1229

def B1227 : Block := .branch 140 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B1228, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq1227 : B1227.tree = HexagonCover.NBand.M8300_8500.SplitData.node1227 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1228
  · rfl
  · rfl

def B1226 : Block := .branch 148 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B1227, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq1226 : B1226.tree = HexagonCover.NBand.M8300_8500.SplitData.node1226 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1227
  · rfl
  · rfl

def B1225 : Block := .branch 168 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79232998217542796110242799624, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 867).pointIds 867), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B1226]
theorem treeEq1225 : B1225.tree = HexagonCover.NBand.M8300_8500.SplitData.node1225 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1226

def B0031 : Block := .branch 82 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B0032, B1225, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M8300_8500.SplitData.node0031 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0032
  · exact treeEq1225
  · rfl
  · rfl
  · rfl

def B0030 : Block := .branch 79 ![578712552117109121, 151152765055713897612802, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![B0031, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), Tip0030_2077]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M8300_8500.SplitData.node0030 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0030 : B0030.accepted = true := by decide +kernel
theorem checked0030 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0030 (maskNeeds ![578712552117109121, 151152765055713897612802, 37778931862957161715716, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0030]
  exact B0030.sound accepted0030
#print axioms checked0030

end HexagonCover.NBand.M8300_8500.SplitTree.Run0028
