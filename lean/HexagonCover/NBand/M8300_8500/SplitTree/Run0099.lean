import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0088
import HexagonCover.NBand.M8300_8500.SplitTree.Run0098
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0099
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4611_4628 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4628 ![576460752303423873, 146437906389534210, 23630279158421935626244, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0088.checked4628
def Tip4611_6357 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6357 ![385, 758927455711921666, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] HexagonCover.NBand.M8300_8500.SplitTree.Run0098.checked6357
def Tip4611_7088 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7088 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] HexagonCover.NBand.M8300_8500.SplitTree.Run0098.checked7088
def B4615 : Block := .branch 79 ![288230376151712129, 144115737831671298, 6148, 24584, 98320, 393248, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1016).pointIds 1016), (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq4615 : B4615.tree = HexagonCover.NBand.M8300_8500.SplitData.node4615 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4614 : Block := .branch 168 ![288230376151712129, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B4615]
theorem treeEq4614 : B4614.tree = HexagonCover.NBand.M8300_8500.SplitData.node4614 := by
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
  · exact treeEq4615

def B4627 : Block := .branch 74 ![576460752303423873, 146437906389534210, 4740813226943354771460, 162338504991727627729171554263048, 1393796574908163946345982392040522594222096, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip4611_4628, (.leaf 3 (Common.fact 1037).pointIds 1037), (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq4627 : B4627.tree = HexagonCover.NBand.M8300_8500.SplitData.node4627 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4626 : Block := .branch 107 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1396518833843531454053689388899976739913744, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B4627, (.leaf 4 (Common.fact 1033).pointIds 1033), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq4626 : B4626.tree = HexagonCover.NBand.M8300_8500.SplitData.node4626 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4627
  · rfl
  · rfl
  · rfl

def B4625 : Block := .branch 73 ![576460752303423873, 146437906389534210, 4740813226943354771460, 332307078174391482490289358614061064, 1396518833843531454053689388899976739913744, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), B4626, (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq4625 : B4625.tree = HexagonCover.NBand.M8300_8500.SplitData.node4625 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4626
  · rfl
  · rfl
  · rfl
  · rfl

def B4624 : Block := .branch 118 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1396518833843531454053689388899976739913744, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B4625, (.leaf 4 (Common.fact 1025).pointIds 1025), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1026).pointIds 1026)]
theorem treeEq4624 : B4624.tree = HexagonCover.NBand.M8300_8500.SplitData.node4624 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4625
  · rfl
  · rfl
  · rfl

def B4623 : Block := .branch 128 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1396518833843531454053689388899976739913744, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B4624, (.leaf 4 (Common.fact 1023).pointIds 1023), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1024).pointIds 1024)]
theorem treeEq4623 : B4623.tree = HexagonCover.NBand.M8300_8500.SplitData.node4623 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4624
  · rfl
  · rfl
  · rfl

def B4622 : Block := .branch 131 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), B4623, (.leaf 5 (Common.fact 733).pointIds 733), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq4622 : B4622.tree = HexagonCover.NBand.M8300_8500.SplitData.node4622 := by
  change Tree.branch (131 : Fin 177) _ = Tree.branch (131 : Fin 177) _
  apply congrArg (Tree.branch (131 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4623
  · rfl
  · rfl

def B4621 : Block := .branch 143 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B4622]
theorem treeEq4621 : B4621.tree = HexagonCover.NBand.M8300_8500.SplitData.node4621 := by
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
  · exact treeEq4622

def B4620 : Block := .branch 140 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 98320, 393248, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B4621, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq4620 : B4620.tree = HexagonCover.NBand.M8300_8500.SplitData.node4620 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4621
  · rfl
  · rfl

def B4619 : Block := .branch 147 ![576460752303423873, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B4620, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq4619 : B4619.tree = HexagonCover.NBand.M8300_8500.SplitData.node4619 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4620
  · rfl
  · rfl

def B4618 : Block := .branch 148 ![576460752303423873, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B4619, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq4618 : B4618.tree = HexagonCover.NBand.M8300_8500.SplitData.node4618 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4619
  · rfl
  · rfl

def B4617 : Block := .branch 168 ![576460752303423873, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1018).pointIds 1018), (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), B4618]
theorem treeEq4617 : B4617.tree = HexagonCover.NBand.M8300_8500.SplitData.node4617 := by
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
  · exact treeEq4618

def B4616 : Block := .branch 59 ![385, 182466703408498178, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![B4617, Tip4611_6357, (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), (.leaf 6 (Common.fact 142).pointIds 142)]
theorem treeEq4616 : B4616.tree = HexagonCover.NBand.M8300_8500.SplitData.node4616 := by
  change Tree.branch (59 : Fin 177) _ = Tree.branch (59 : Fin 177) _
  apply congrArg (Tree.branch (59 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4617
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4613 : Block := .branch 58 ![385, 182466703408498178, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![B4614, B4616, (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), (.leaf 6 (Common.fact 132).pointIds 132)]
theorem treeEq4613 : B4613.tree = HexagonCover.NBand.M8300_8500.SplitData.node4613 := by
  change Tree.branch (58 : Fin 177) _ = Tree.branch (58 : Fin 177) _
  apply congrArg (Tree.branch (58 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4614
  · exact treeEq4616
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7087 : Block := .branch 147 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), Tip4611_7088, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1462).pointIds 1462)]
theorem treeEq7087 : B7087.tree = HexagonCover.NBand.M8300_8500.SplitData.node7087 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7086 : Block := .branch 160 ![385, 146437906389534210, 4740849255740373735428, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 1461).pointIds 1461), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B7087]
theorem treeEq7086 : B7086.tree = HexagonCover.NBand.M8300_8500.SplitData.node7086 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7087

def B4612 : Block := .branch 55 ![385, 146437906389534210, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 133).pointIds 133), B4613, B7086, (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 137).pointIds 137)]
theorem treeEq4612 : B4612.tree = HexagonCover.NBand.M8300_8500.SplitData.node4612 := by
  change Tree.branch (55 : Fin 177) _ = Tree.branch (55 : Fin 177) _
  apply congrArg (Tree.branch (55 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4613
  · exact treeEq7086
  · rfl
  · rfl
  · rfl
  · rfl

def B4611 : Block := .branch 171 ![385, 146437906389534210, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1008).pointIds 1008), (.leaf 1 (Common.fact 1009).pointIds 1009), (.leaf 2 (Common.fact 1010).pointIds 1010), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 1011).pointIds 1011), (.leaf 5 (Common.fact 563).pointIds 563), B4612]
theorem treeEq4611 : B4611.tree = HexagonCover.NBand.M8300_8500.SplitData.node4611 := by
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
  · exact treeEq4612

theorem accepted4611 : B4611.accepted = true := by decide +kernel
theorem checked4611 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4611 (maskNeeds ![385, 146437906389534210, 4740813226943354771460, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq4611]
  exact B4611.sound accepted4611
#print axioms checked4611

def B7192 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7192 : B7192.tree = HexagonCover.NBand.M8300_8500.SplitData.node7192 := by
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

def B7191 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7192, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7191 : B7191.tree = HexagonCover.NBand.M8300_8500.SplitData.node7191 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7192
  · rfl
  · rfl

def B7190 : Block := .branch 173 ![604462909807314587353473, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7191]
theorem treeEq7190 : B7190.tree = HexagonCover.NBand.M8300_8500.SplitData.node7190 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7191

def B7194 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7194 : B7194.tree = HexagonCover.NBand.M8300_8500.SplitData.node7194 := by
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

def B7193 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7194, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7193 : B7193.tree = HexagonCover.NBand.M8300_8500.SplitData.node7193 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7194
  · rfl
  · rfl

def B7189 : Block := .branch 79 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7190, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7193]
theorem treeEq7189 : B7189.tree = HexagonCover.NBand.M8300_8500.SplitData.node7189 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7190
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7193

def B7196 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7196 : B7196.tree = HexagonCover.NBand.M8300_8500.SplitData.node7196 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7195 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7196, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7195 : B7195.tree = HexagonCover.NBand.M8300_8500.SplitData.node7195 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7196
  · rfl
  · rfl

def B7188 : Block := .branch 77 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7189, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7195]
theorem treeEq7188 : B7188.tree = HexagonCover.NBand.M8300_8500.SplitData.node7188 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7189
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7195

def B7198 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7198 : B7198.tree = HexagonCover.NBand.M8300_8500.SplitData.node7198 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7197 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7198, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7197 : B7197.tree = HexagonCover.NBand.M8300_8500.SplitData.node7197 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7198
  · rfl
  · rfl

def B7187 : Block := .branch 75 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7188, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7197]
theorem treeEq7187 : B7187.tree = HexagonCover.NBand.M8300_8500.SplitData.node7187 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7188
  · rfl
  · rfl
  · rfl
  · exact treeEq7197

def B7200 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7200 : B7200.tree = HexagonCover.NBand.M8300_8500.SplitData.node7200 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7199 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7200, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7199 : B7199.tree = HexagonCover.NBand.M8300_8500.SplitData.node7199 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7200
  · rfl
  · rfl

def B7186 : Block := .branch 66 ![385, 144115737831671298, 23630279228790679803908, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7187, (.leaf 2 (Common.fact 1530).pointIds 1530), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7199]
theorem treeEq7186 : B7186.tree = HexagonCover.NBand.M8300_8500.SplitData.node7186 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7187
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7199

theorem accepted7186 : B7186.accepted = true := by decide +kernel
theorem checked7186 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7186 (maskNeeds ![385, 144115737831671298, 23630279228790679803908, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7186]
  exact B7186.sound accepted7186
#print axioms checked7186

def Tip7185_7186 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7186 ![385, 144115737831671298, 23630279228790679803908, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7186
def B7211 : Block := .branch 129 ![385, 1538, 6148, 18889465931478580879368, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 1491).pointIds 1491), (.leaf 4 (Common.fact 1492).pointIds 1492), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1493).pointIds 1493)]
theorem treeEq7211 : B7211.tree = HexagonCover.NBand.M8300_8500.SplitData.node7211 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7210 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7211, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7210 : B7210.tree = HexagonCover.NBand.M8300_8500.SplitData.node7210 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7211
  · rfl
  · rfl

def B7209 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1516).pointIds 1516), (.leaf 2 (Common.fact 1517).pointIds 1517), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7210]
theorem treeEq7209 : B7209.tree = HexagonCover.NBand.M8300_8500.SplitData.node7209 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7210

def B7208 : Block := .branch 173 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7209, (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7208 : B7208.tree = HexagonCover.NBand.M8300_8500.SplitData.node7208 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7209
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7207 : Block := .branch 162 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1409).pointIds 1409), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7208]
theorem treeEq7207 : B7207.tree = HexagonCover.NBand.M8300_8500.SplitData.node7207 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7208

def B7206 : Block := .branch 165 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7207, (.leaf 0 [] 0)]
theorem treeEq7206 : B7206.tree = HexagonCover.NBand.M8300_8500.SplitData.node7206 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7207
  · rfl

def B7205 : Block := .branch 167 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7206, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7205 : B7205.tree = HexagonCover.NBand.M8300_8500.SplitData.node7205 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7206
  · rfl

def B7204 : Block := .branch 146 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1408).pointIds 1408), B7205, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7204 : B7204.tree = HexagonCover.NBand.M8300_8500.SplitData.node7204 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7205
  · rfl
  · rfl

def B7203 : Block := .branch 150 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7204, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7203 : B7203.tree = HexagonCover.NBand.M8300_8500.SplitData.node7203 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7204
  · rfl
  · rfl

def B7202 : Block := .branch 168 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7203, (.leaf 1 (Common.fact 1531).pointIds 1531), (.leaf 2 (Common.fact 1532).pointIds 1532), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7202 : B7202.tree = HexagonCover.NBand.M8300_8500.SplitData.node7202 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7203
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7201 : Block := .branch 170 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228181403730269072124829704, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), (.leaf 3 (Common.fact 1406).pointIds 1406), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7202]
theorem treeEq7201 : B7201.tree = HexagonCover.NBand.M8300_8500.SplitData.node7201 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7202

def B7185 : Block := .branch 74 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1035).pointIds 1035), (.leaf 1 (Common.fact 1036).pointIds 1036), Tip7185_7186, B7201, (.leaf 4 (Common.fact 1038).pointIds 1038), (.leaf 5 (Common.fact 1039).pointIds 1039), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq7185 : B7185.tree = HexagonCover.NBand.M8300_8500.SplitData.node7185 := by
  change Tree.branch (74 : Fin 177) _ = Tree.branch (74 : Fin 177) _
  apply congrArg (Tree.branch (74 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7201
  · rfl
  · rfl
  · rfl

theorem accepted7185 : B7185.accepted = true := by decide +kernel
theorem checked7185 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7185 (maskNeeds ![590295810358705652097, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7185]
  exact B7185.sound accepted7185
#print axioms checked7185

def Tip7182_7185 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7185 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] checked7185
def B7222 : Block := .branch 118 ![385, 1538, 6148, 79228171958997303332834402312, 23945242915232494205971664865366454084636244808138768, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 1029).pointIds 1029), (.leaf 4 (Common.fact 1494).pointIds 1494), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1495).pointIds 1495)]
theorem treeEq7222 : B7222.tree = HexagonCover.NBand.M8300_8500.SplitData.node7222 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7221 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 5993618214715816255948234700294624253713403400945728] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7222, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1490).pointIds 1490)]
theorem treeEq7221 : B7221.tree = HexagonCover.NBand.M8300_8500.SplitData.node7221 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7222
  · rfl
  · rfl

def B7220 : Block := .branch 172 ![11972621413014756705924586149612380792831758097711489, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![(.leaf 0 (Common.fact 1486).pointIds 1486), (.leaf 1 (Common.fact 1516).pointIds 1516), (.leaf 2 (Common.fact 1517).pointIds 1517), (.leaf 3 (Common.fact 1489).pointIds 1489), (.leaf 4 (Common.fact 1518).pointIds 1518), (.leaf 5 (Common.fact 1239).pointIds 1239), B7221]
theorem treeEq7220 : B7220.tree = HexagonCover.NBand.M8300_8500.SplitData.node7220 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7221

def B7219 : Block := .branch 173 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 89202980794122492566142873090593446024019984, 393248, 7307508208437902985941625488729005202703704916032] ![B7220, (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), (.leaf 6 (Common.fact 1485).pointIds 1485)]
theorem treeEq7219 : B7219.tree = HexagonCover.NBand.M8300_8500.SplitData.node7219 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7218 : Block := .branch 162 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 1430).pointIds 1430), (.leaf 4 (Common.fact 1484).pointIds 1484), (.leaf 5 (Common.fact 358).pointIds 358), B7219]
theorem treeEq7218 : B7218.tree = HexagonCover.NBand.M8300_8500.SplitData.node7218 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7219

def B7217 : Block := .branch 165 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1483).pointIds 1483), B7218, (.leaf 0 [] 0)]
theorem treeEq7217 : B7217.tree = HexagonCover.NBand.M8300_8500.SplitData.node7217 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7218
  · rfl

def B7216 : Block := .branch 167 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1516450673500082373624428842540088582406766608, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1482).pointIds 1482), B7217, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq7216 : B7216.tree = HexagonCover.NBand.M8300_8500.SplitData.node7216 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7217
  · rfl

def B7215 : Block := .branch 146 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 1427247692705959881058285969449495136382844944, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 1429).pointIds 1429), B7216, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq7215 : B7215.tree = HexagonCover.NBand.M8300_8500.SplitData.node7215 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7216
  · rfl
  · rfl

def B7214 : Block := .branch 150 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B7215, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1481).pointIds 1481)]
theorem treeEq7214 : B7214.tree = HexagonCover.NBand.M8300_8500.SplitData.node7214 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7215
  · rfl
  · rfl

def B7213 : Block := .branch 168 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1498039178285958879553700154859337685251754898751552] ![B7214, (.leaf 1 (Common.fact 1531).pointIds 1531), (.leaf 2 (Common.fact 1532).pointIds 1532), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1480).pointIds 1480)]
theorem treeEq7213 : B7213.tree = HexagonCover.NBand.M8300_8500.SplitData.node7213 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7212 : Block := .branch 170 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 79228171958997303332834402312, 98320, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1519).pointIds 1519), (.leaf 2 (Common.fact 1520).pointIds 1520), (.leaf 3 (Common.fact 1428).pointIds 1428), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7213]
theorem treeEq7212 : B7212.tree = HexagonCover.NBand.M8300_8500.SplitData.node7212 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7213

def B7184 : Block := .branch 73 ![590295810358705652097, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1027).pointIds 1027), (.leaf 1 (Common.fact 1028).pointIds 1028), Tip7182_7185, B7212, (.leaf 4 (Common.fact 1030).pointIds 1030), (.leaf 5 (Common.fact 1031).pointIds 1031), (.leaf 6 (Common.fact 1032).pointIds 1032)]
theorem treeEq7184 : B7184.tree = HexagonCover.NBand.M8300_8500.SplitData.node7184 := by
  change Tree.branch (73 : Fin 177) _ = Tree.branch (73 : Fin 177) _
  apply congrArg (Tree.branch (73 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7212
  · rfl
  · rfl
  · rfl

def B7224 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1497).pointIds 1497)]
theorem treeEq7224 : B7224.tree = HexagonCover.NBand.M8300_8500.SplitData.node7224 := by
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

def B7223 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886158454168934438680395840] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7224, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1496).pointIds 1496)]
theorem treeEq7223 : B7223.tree = HexagonCover.NBand.M8300_8500.SplitData.node7223 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7224
  · rfl
  · rfl

def B7183 : Block := .branch 69 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7184, (.leaf 1 (Common.fact 158).pointIds 158), (.leaf 2 (Common.fact 159).pointIds 159), (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), B7223]
theorem treeEq7183 : B7183.tree = HexagonCover.NBand.M8300_8500.SplitData.node7183 := by
  change Tree.branch (69 : Fin 177) _ = Tree.branch (69 : Fin 177) _
  apply congrArg (Tree.branch (69 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7184
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7223

def B7226 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1460).pointIds 1460)]
theorem treeEq7226 : B7226.tree = HexagonCover.NBand.M8300_8500.SplitData.node7226 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7225 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325295164057013718614080] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7226, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1498).pointIds 1498)]
theorem treeEq7225 : B7225.tree = HexagonCover.NBand.M8300_8500.SplitData.node7225 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7226
  · rfl
  · rfl

def B7182 : Block := .branch 67 ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 153).pointIds 153), B7183, (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), B7225]
theorem treeEq7182 : B7182.tree = HexagonCover.NBand.M8300_8500.SplitData.node7182 := by
  change Tree.branch (67 : Fin 177) _ = Tree.branch (67 : Fin 177) _
  apply congrArg (Tree.branch (67 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7183
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7225

theorem accepted7182 : B7182.accepted = true := by decide +kernel
theorem checked7182 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7182 (maskNeeds ![385, 144115737831671298, 4740813297312098949124, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7182]
  exact B7182.sound accepted7182
#print axioms checked7182

def B7245 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq7245 : B7245.tree = HexagonCover.NBand.M8300_8500.SplitData.node7245 := by
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

def B7244 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7245, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq7244 : B7244.tree = HexagonCover.NBand.M8300_8500.SplitData.node7244 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7245
  · rfl
  · rfl

def B7243 : Block := .branch 173 ![604462909807314587353473, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1510).pointIds 1510), (.leaf 2 (Common.fact 1511).pointIds 1511), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1512).pointIds 1512), (.leaf 5 (Common.fact 1238).pointIds 1238), B7244]
theorem treeEq7243 : B7243.tree = HexagonCover.NBand.M8300_8500.SplitData.node7243 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7244

def B7247 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1473).pointIds 1473)]
theorem treeEq7247 : B7247.tree = HexagonCover.NBand.M8300_8500.SplitData.node7247 := by
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

def B7246 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886762326782931394562097216] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7247, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1472).pointIds 1472)]
theorem treeEq7246 : B7246.tree = HexagonCover.NBand.M8300_8500.SplitData.node7246 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7247
  · rfl
  · rfl

def B7242 : Block := .branch 79 ![385, 144115737831671298, 4740813297312098949124, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![B7243, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B7246]
theorem treeEq7242 : B7242.tree = HexagonCover.NBand.M8300_8500.SplitData.node7242 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq7243
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7246

def B7249 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1476).pointIds 1476)]
theorem treeEq7249 : B7249.tree = HexagonCover.NBand.M8300_8500.SplitData.node7249 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7248 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201476263317556252689039424] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7249, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1474).pointIds 1474)]
theorem treeEq7248 : B7248.tree = HexagonCover.NBand.M8300_8500.SplitData.node7248 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7249
  · rfl
  · rfl

def B7241 : Block := .branch 77 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 163).pointIds 163), B7242, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), B7248]
theorem treeEq7241 : B7241.tree = HexagonCover.NBand.M8300_8500.SplitData.node7241 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7242
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7248

def B7251 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1478).pointIds 1478)]
theorem treeEq7251 : B7251.tree = HexagonCover.NBand.M8300_8500.SplitData.node7251 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7250 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886195642804987037136453696] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7251, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1477).pointIds 1477)]
theorem treeEq7250 : B7250.tree = HexagonCover.NBand.M8300_8500.SplitData.node7250 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7251
  · rfl
  · rfl

def B7240 : Block := .branch 75 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), B7241, (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7250]
theorem treeEq7240 : B7240.tree = HexagonCover.NBand.M8300_8500.SplitData.node7240 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7241
  · rfl
  · rfl
  · rfl
  · exact treeEq7250

def B7253 : Block := .branch 139 ![385, 1538, 6148, 81129638414606681695789005168648, 23945243004435475000094157431509327175229690832060432, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 1475).pointIds 1475), (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1405).pointIds 1405)]
theorem treeEq7253 : B7253.tree = HexagonCover.NBand.M8300_8500.SplitData.node7253 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7252 : Block := .branch 174 ![385, 144115737831671298, 4740813297312098949124, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325221377080718880407616] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1514).pointIds 1514), (.leaf 2 (Common.fact 1515).pointIds 1515), (.leaf 3 (Common.fact 1353).pointIds 1353), B7253, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1479).pointIds 1479)]
theorem treeEq7252 : B7252.tree = HexagonCover.NBand.M8300_8500.SplitData.node7252 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7253
  · rfl
  · rfl

def B7239 : Block := .branch 66 ![385, 144115737831671298, 23630315257587698767876, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 148).pointIds 148), B7240, (.leaf 2 (Common.fact 1533).pointIds 1533), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), B7252]
theorem treeEq7239 : B7239.tree = HexagonCover.NBand.M8300_8500.SplitData.node7239 := by
  change Tree.branch (66 : Fin 177) _ = Tree.branch (66 : Fin 177) _
  apply congrArg (Tree.branch (66 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7240
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7252

theorem accepted7239 : B7239.accepted = true := by decide +kernel
theorem checked7239 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node7239 (maskNeeds ![385, 144115737831671298, 23630315257587698767876, 81208866577120946033382549118984, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128]) := by
  rw [← treeEq7239]
  exact B7239.sound accepted7239
#print axioms checked7239

end HexagonCover.NBand.M8300_8500.SplitTree.Run0099
