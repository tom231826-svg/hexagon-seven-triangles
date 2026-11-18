import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0013
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0014
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B1148 : Block := .branch 79 ![374144419156732414710611177030381668558235328577921, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq1148 : B1148.tree = HexagonCover.NBand.M7100_7300.SplitData.node1148 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1147 : Block := .branch 159 ![374144419156732414710611177030381668558235328577921, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 714).pointIds 714), B1148, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1147 : B1147.tree = HexagonCover.NBand.M7100_7300.SplitData.node1147 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1148
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1146 : Block := .branch 124 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B1147, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq1146 : B1146.tree = HexagonCover.NBand.M7100_7300.SplitData.node1146 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1147
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1145 : Block := .branch 128 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B1146, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq1145 : B1145.tree = HexagonCover.NBand.M7100_7300.SplitData.node1145 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1146
  · rfl
  · rfl
  · rfl

def B1144 : Block := .branch 138 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B1145, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1144 : B1144.tree = HexagonCover.NBand.M7100_7300.SplitData.node1144 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1145
  · rfl
  · rfl

def B1143 : Block := .branch 139 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B1144, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1143 : B1143.tree = HexagonCover.NBand.M7100_7300.SplitData.node1143 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1144
  · rfl
  · rfl

def B1142 : Block := .branch 140 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B1143, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq1142 : B1142.tree = HexagonCover.NBand.M7100_7300.SplitData.node1142 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1143
  · rfl
  · rfl

def B1141 : Block := .branch 141 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B1142, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq1141 : B1141.tree = HexagonCover.NBand.M7100_7300.SplitData.node1141 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1142
  · rfl
  · rfl

def B1140 : Block := .branch 142 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1141, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1140 : B1140.tree = HexagonCover.NBand.M7100_7300.SplitData.node1140 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1141
  · rfl
  · rfl

def B1139 : Block := .branch 165 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B1140, (.leaf 0 [] 0)]
theorem treeEq1139 : B1139.tree = HexagonCover.NBand.M7100_7300.SplitData.node1139 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1140
  · rfl

def B1138 : Block := .branch 167 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B1139, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1138 : B1138.tree = HexagonCover.NBand.M7100_7300.SplitData.node1138 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1139
  · rfl

def B1137 : Block := .branch 143 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B1138, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq1137 : B1137.tree = HexagonCover.NBand.M7100_7300.SplitData.node1137 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1138
  · rfl
  · rfl

def B1136 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1137]
theorem treeEq1136 : B1136.tree = HexagonCover.NBand.M7100_7300.SplitData.node1136 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1137

def B1135 : Block := .branch 161 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B1136, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq1135 : B1135.tree = HexagonCover.NBand.M7100_7300.SplitData.node1135 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1136
  · rfl
  · rfl
  · rfl

def B1134 : Block := .branch 75 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B1135, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq1134 : B1134.tree = HexagonCover.NBand.M7100_7300.SplitData.node1134 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1135
  · rfl
  · rfl
  · rfl
  · rfl

def B1133 : Block := .branch 162 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B1134, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq1133 : B1133.tree = HexagonCover.NBand.M7100_7300.SplitData.node1133 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1134
  · rfl
  · rfl
  · rfl

def B1132 : Block := .branch 172 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B1133]
theorem treeEq1132 : B1132.tree = HexagonCover.NBand.M7100_7300.SplitData.node1132 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1133

def B1131 : Block := .branch 151 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B1132, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq1131 : B1131.tree = HexagonCover.NBand.M7100_7300.SplitData.node1131 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1132
  · rfl
  · rfl

def B1130 : Block := .branch 132 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B1131]
theorem treeEq1130 : B1130.tree = HexagonCover.NBand.M7100_7300.SplitData.node1130 := by
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
  · exact treeEq1131

def B1129 : Block := .branch 78 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B1130, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq1129 : B1129.tree = HexagonCover.NBand.M7100_7300.SplitData.node1129 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1130
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1129 : B1129.accepted = true := by decide +kernel
theorem checked1129 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1129 (maskNeeds ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq1129]
  exact B1129.sound accepted1129
#print axioms checked1129

def Tip1120_1129 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1129 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked1129
def B1128 : Block := .branch 101 ![374144419156711147060143317175958748842277436653953, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip1120_1129, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq1128 : B1128.tree = HexagonCover.NBand.M7100_7300.SplitData.node1128 := by
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
  · rfl

def B1127 : Block := .branch 168 ![590295810358705652097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B1128, (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1127 : B1127.tree = HexagonCover.NBand.M7100_7300.SplitData.node1127 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1128
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1126 : Block := .branch 133 ![590295810358705652097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B1127]
theorem treeEq1126 : B1126.tree = HexagonCover.NBand.M7100_7300.SplitData.node1126 := by
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
  · exact treeEq1127

def B1125 : Block := .branch 157 ![590295810358705652097, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B1126, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq1125 : B1125.tree = HexagonCover.NBand.M7100_7300.SplitData.node1125 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1126
  · rfl
  · rfl

def B1124 : Block := .branch 169 ![10384593717070245552871351364092289, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B1125, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq1124 : B1124.tree = HexagonCover.NBand.M7100_7300.SplitData.node1124 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1125
  · rfl

def B1157 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M7100_7300.SplitData.node1157 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1156 : Block := .branch 159 ![10384593717069655257060992658440577, 737941820542419994114, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B1157, (.leaf 1 (Common.fact 924).pointIds 924), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq1156 : B1156.tree = HexagonCover.NBand.M7100_7300.SplitData.node1156 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1157
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1155 : Block := .branch 75 ![10384593717069655257060992658440577, 737941820542419994114, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B1156, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq1155 : B1155.tree = HexagonCover.NBand.M7100_7300.SplitData.node1155 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1156
  · rfl
  · rfl
  · rfl
  · rfl

def B1154 : Block := .branch 170 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1155]
theorem treeEq1154 : B1154.tree = HexagonCover.NBand.M7100_7300.SplitData.node1154 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1155

def B1153 : Block := .branch 161 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B1154, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq1153 : B1153.tree = HexagonCover.NBand.M7100_7300.SplitData.node1153 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1154
  · rfl
  · rfl
  · rfl

def B1152 : Block := .branch 168 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![B1153, (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq1152 : B1152.tree = HexagonCover.NBand.M7100_7300.SplitData.node1152 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1153
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1151 : Block := .branch 172 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1152]
theorem treeEq1151 : B1151.tree = HexagonCover.NBand.M7100_7300.SplitData.node1151 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1152

def B1150 : Block := .branch 171 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1151, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1150 : B1150.tree = HexagonCover.NBand.M7100_7300.SplitData.node1150 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1151
  · rfl
  · rfl

def B1149 : Block := .branch 160 ![10384593717069655257060992658440577, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 923).pointIds 923), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1150]
theorem treeEq1149 : B1149.tree = HexagonCover.NBand.M7100_7300.SplitData.node1149 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1150

def B1123 : Block := .branch 69 ![10384593717069655257060992658440577, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1124, B1149, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1123 : B1123.tree = HexagonCover.NBand.M7100_7300.SplitData.node1123 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1124
  · exact treeEq1149
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1159 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M7100_7300.SplitData.node1159 := by
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

def B1158 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B1159, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M7100_7300.SplitData.node1158 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1159
  · rfl
  · rfl

def B1122 : Block := .branch 68 ![10384593717069655257060992658440577, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B1123, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B1158]
theorem treeEq1122 : B1122.tree = HexagonCover.NBand.M7100_7300.SplitData.node1122 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1123
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1158

def B1121 : Block := .branch 91 ![10384593717069655257060992658440577, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1122, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq1121 : B1121.tree = HexagonCover.NBand.M7100_7300.SplitData.node1121 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1122
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1120 : Block := .branch 113 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B1121, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq1120 : B1120.tree = HexagonCover.NBand.M7100_7300.SplitData.node1120 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1121
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1120 : B1120.accepted = true := by decide +kernel
theorem checked1120 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1120 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq1120]
  exact B1120.sound accepted1120
#print axioms checked1120

def Tip1089_1092 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1092 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0013.checked1092
def Tip1089_1120 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1120 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] checked1120
def B1115 : Block := .branch 160 ![385, 302821822771610037257730, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 922).pointIds 922), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1115 : B1115.tree = HexagonCover.NBand.M7100_7300.SplitData.node1115 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1114 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231526961251331606018, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B1115, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1114 : B1114.tree = HexagonCover.NBand.M7100_7300.SplitData.node1114 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1115
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1113 : Block := .branch 169 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B1114, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq1113 : B1113.tree = HexagonCover.NBand.M7100_7300.SplitData.node1113 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1114
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1112 : Block := .branch 151 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B1113, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq1112 : B1112.tree = HexagonCover.NBand.M7100_7300.SplitData.node1112 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1113
  · rfl

def B1111 : Block := .branch 172 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1112]
theorem treeEq1111 : B1111.tree = HexagonCover.NBand.M7100_7300.SplitData.node1111 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1112

def B1110 : Block := .branch 171 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1111, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq1110 : B1110.tree = HexagonCover.NBand.M7100_7300.SplitData.node1110 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1111
  · rfl
  · rfl

def B1091 : Block := .branch 80 ![385, 302231671076439407461890, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1089_1092, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1110]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M7100_7300.SplitData.node1091 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1110

def B1119 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq1119 : B1119.tree = HexagonCover.NBand.M7100_7300.SplitData.node1119 := by
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

def B1118 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1119, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1118 : B1118.tree = HexagonCover.NBand.M7100_7300.SplitData.node1118 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1119
  · rfl
  · rfl

def B1117 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B1118]
theorem treeEq1117 : B1117.tree = HexagonCover.NBand.M7100_7300.SplitData.node1117 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1118

def B1116 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1117, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq1116 : B1116.tree = HexagonCover.NBand.M7100_7300.SplitData.node1116 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1117
  · rfl
  · rfl

def B1090 : Block := .branch 78 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B1091, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B1116]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M7100_7300.SplitData.node1090 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1091
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1116

def B1089 : Block := .branch 76 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B1090, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip1089_1120]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M7100_7300.SplitData.node1089 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1090
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1089 : B1089.accepted = true := by decide +kernel
theorem checked1089 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1089 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1089]
  exact B1089.sound accepted1089
#print axioms checked1089

def Tip1088_1089 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1089 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1089
def B1172 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq1172 : B1172.tree = HexagonCover.NBand.M7100_7300.SplitData.node1172 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1171 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B1172]
theorem treeEq1171 : B1171.tree = HexagonCover.NBand.M7100_7300.SplitData.node1171 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1172

def B1170 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B1171, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq1170 : B1170.tree = HexagonCover.NBand.M7100_7300.SplitData.node1170 := by
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

def B1169 : Block := .branch 160 ![385, 604463125980096701138434, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 925).pointIds 925), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B1170]
theorem treeEq1169 : B1169.tree = HexagonCover.NBand.M7100_7300.SplitData.node1169 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1170

def B1168 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B1169, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M7100_7300.SplitData.node1168 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1169
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1167 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B1168, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M7100_7300.SplitData.node1167 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1168
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1166 : Block := .branch 168 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B1167, (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M7100_7300.SplitData.node1166 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1167
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1165 : Block := .branch 163 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B1166]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M7100_7300.SplitData.node1165 := by
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
  · exact treeEq1166

def B1164 : Block := .branch 165 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B1165, (.leaf 0 [] 0)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M7100_7300.SplitData.node1164 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1165
  · rfl

def B1163 : Block := .branch 167 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B1164, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M7100_7300.SplitData.node1163 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1164
  · rfl

def B1162 : Block := .branch 142 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B1163, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M7100_7300.SplitData.node1162 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1163
  · rfl
  · rfl

def B1161 : Block := .branch 144 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B1162, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M7100_7300.SplitData.node1161 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1162
  · rfl

def B1160 : Block := .branch 170 ![385, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B1161]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M7100_7300.SplitData.node1160 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1161

def B1088 : Block := .branch 74 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip1088_1089, B1160, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M7100_7300.SplitData.node1088 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1160
  · rfl
  · rfl
  · rfl

theorem accepted1088 : B1088.accepted = true := by decide +kernel
theorem checked1088 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node1088 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1088]
  exact B1088.sound accepted1088
#print axioms checked1088

end HexagonCover.NBand.M7100_7300.SplitTree.Run0014
