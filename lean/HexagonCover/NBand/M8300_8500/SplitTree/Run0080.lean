import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0079
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0080
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip5712_5715 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5715 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0079.checked5715
def B5829 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 891).pointIds 891)]
theorem treeEq5829 : B5829.tree = HexagonCover.NBand.M8300_8500.SplitData.node5829 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5828 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5829, (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq5828 : B5828.tree = HexagonCover.NBand.M8300_8500.SplitData.node5828 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5829
  · rfl

def B5827 : Block := .branch 87 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B5828, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq5827 : B5827.tree = HexagonCover.NBand.M8300_8500.SplitData.node5827 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5828
  · rfl
  · rfl
  · rfl
  · rfl

def B5826 : Block := .branch 129 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B5827, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5826 : B5826.tree = HexagonCover.NBand.M8300_8500.SplitData.node5826 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5827
  · rfl
  · rfl

def B5825 : Block := .branch 138 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B5826, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5825 : B5825.tree = HexagonCover.NBand.M8300_8500.SplitData.node5825 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5826
  · rfl
  · rfl

def B5824 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5825, (.leaf 0 [] 0)]
theorem treeEq5824 : B5824.tree = HexagonCover.NBand.M8300_8500.SplitData.node5824 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5825
  · rfl

def B5823 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5824, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5823 : B5823.tree = HexagonCover.NBand.M8300_8500.SplitData.node5823 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5824
  · rfl

def B5822 : Block := .branch 146 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B5823, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5822 : B5822.tree = HexagonCover.NBand.M8300_8500.SplitData.node5822 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5823
  · rfl
  · rfl

def B5821 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5822, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq5821 : B5821.tree = HexagonCover.NBand.M8300_8500.SplitData.node5821 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5822
  · rfl
  · rfl
  · rfl

def B5714 : Block := .branch 90 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5712_5715, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B5821]
theorem treeEq5714 : B5714.tree = HexagonCover.NBand.M8300_8500.SplitData.node5714 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5821

def B5832 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5832 : B5832.tree = HexagonCover.NBand.M8300_8500.SplitData.node5832 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5831 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5832, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5831 : B5831.tree = HexagonCover.NBand.M8300_8500.SplitData.node5831 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5832
  · rfl

def B5830 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79310369469998132377423994888, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5831]
theorem treeEq5830 : B5830.tree = HexagonCover.NBand.M8300_8500.SplitData.node5830 := by
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
  · exact treeEq5831

def B5713 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B5714, B5830, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq5713 : B5713.tree = HexagonCover.NBand.M8300_8500.SplitData.node5713 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5714
  · exact treeEq5830
  · rfl
  · rfl
  · rfl

def B5835 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5835 : B5835.tree = HexagonCover.NBand.M8300_8500.SplitData.node5835 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5834 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5835, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5834 : B5834.tree = HexagonCover.NBand.M8300_8500.SplitData.node5834 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5835
  · rfl

def B5833 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237728008872299139430921297928, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 893).pointIds 893), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5834]
theorem treeEq5833 : B5833.tree = HexagonCover.NBand.M8300_8500.SplitData.node5833 := by
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
  · exact treeEq5834

def B5712 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B5713, B5833, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq5712 : B5712.tree = HexagonCover.NBand.M8300_8500.SplitData.node5712 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5713
  · exact treeEq5833
  · rfl
  · rfl
  · rfl

theorem accepted5712 : B5712.accepted = true := by decide +kernel
theorem checked5712 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5712 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5712]
  exact B5712.sound accepted5712
#print axioms checked5712

def B5851 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5851 : B5851.tree = HexagonCover.NBand.M8300_8500.SplitData.node5851 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5850 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5851, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5850 : B5850.tree = HexagonCover.NBand.M8300_8500.SplitData.node5850 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5851
  · rfl

def B5849 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614394047777617608967047956422664, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 895).pointIds 895), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5850]
theorem treeEq5849 : B5849.tree = HexagonCover.NBand.M8300_8500.SplitData.node5849 := by
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
  · exact treeEq5850

def B5856 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5856 : B5856.tree = HexagonCover.NBand.M8300_8500.SplitData.node5856 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5855 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5856, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5855 : B5855.tree = HexagonCover.NBand.M8300_8500.SplitData.node5855 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5856
  · rfl

def B5854 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B5855]
theorem treeEq5854 : B5854.tree = HexagonCover.NBand.M8300_8500.SplitData.node5854 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5855

def B5853 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B5854, (.leaf 0 [] 0)]
theorem treeEq5853 : B5853.tree = HexagonCover.NBand.M8300_8500.SplitData.node5853 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5854
  · rfl

def B5852 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B5853, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5852 : B5852.tree = HexagonCover.NBand.M8300_8500.SplitData.node5852 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5853
  · rfl

def B5848 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B5849, B5852, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5848 : B5848.tree = HexagonCover.NBand.M8300_8500.SplitData.node5848 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5849
  · exact treeEq5852
  · rfl
  · rfl

def B5860 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5860 : B5860.tree = HexagonCover.NBand.M8300_8500.SplitData.node5860 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5859 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5860, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5859 : B5859.tree = HexagonCover.NBand.M8300_8500.SplitData.node5859 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5860
  · rfl

def B5858 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614394047777617608967047956422664, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 895).pointIds 895), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5859]
theorem treeEq5858 : B5858.tree = HexagonCover.NBand.M8300_8500.SplitData.node5858 := by
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
  · exact treeEq5859

def B5865 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5865 : B5865.tree = HexagonCover.NBand.M8300_8500.SplitData.node5865 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5864 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5865, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5864 : B5864.tree = HexagonCover.NBand.M8300_8500.SplitData.node5864 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5865
  · rfl

def B5863 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B5864]
theorem treeEq5863 : B5863.tree = HexagonCover.NBand.M8300_8500.SplitData.node5863 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5864

def B5862 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B5863, (.leaf 0 [] 0)]
theorem treeEq5862 : B5862.tree = HexagonCover.NBand.M8300_8500.SplitData.node5862 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5863
  · rfl

def B5861 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B5862, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5861 : B5861.tree = HexagonCover.NBand.M8300_8500.SplitData.node5861 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5862
  · rfl

def B5857 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B5858, B5861, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5857 : B5857.tree = HexagonCover.NBand.M8300_8500.SplitData.node5857 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5858
  · exact treeEq5861
  · rfl
  · rfl

def B5847 : Block := .branch 115 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![B5848, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B5857, (.leaf 0 [] 0)]
theorem treeEq5847 : B5847.tree = HexagonCover.NBand.M8300_8500.SplitData.node5847 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq5848
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5857
  · rfl

theorem accepted5847 : B5847.accepted = true := by decide +kernel
theorem checked5847 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5847 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5847]
  exact B5847.sound accepted5847
#print axioms checked5847

def Tip5845_5847 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5847 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked5847
def B5875 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq5875 : B5875.tree = HexagonCover.NBand.M8300_8500.SplitData.node5875 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5874 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B5875, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5874 : B5874.tree = HexagonCover.NBand.M8300_8500.SplitData.node5874 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5875
  · rfl
  · rfl

def B5873 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B5874, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5873 : B5873.tree = HexagonCover.NBand.M8300_8500.SplitData.node5873 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5874
  · rfl
  · rfl

def B5872 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B5873, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5872 : B5872.tree = HexagonCover.NBand.M8300_8500.SplitData.node5872 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5873
  · rfl
  · rfl

def B5871 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5872, (.leaf 0 [] 0)]
theorem treeEq5871 : B5871.tree = HexagonCover.NBand.M8300_8500.SplitData.node5871 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5872
  · rfl

def B5870 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5871, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5870 : B5870.tree = HexagonCover.NBand.M8300_8500.SplitData.node5870 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5871
  · rfl

def B5869 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B5870, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5869 : B5869.tree = HexagonCover.NBand.M8300_8500.SplitData.node5869 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5870
  · rfl
  · rfl

def B5868 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 14507109835375550096498696, 649037107316853453566312041250832, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5869, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq5868 : B5868.tree = HexagonCover.NBand.M8300_8500.SplitData.node5868 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5869
  · rfl
  · rfl
  · rfl

def B5867 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 43556142965880123323311949751266331459616, 3367299772432183722320806772973118924452685279658048] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B5868]
theorem treeEq5867 : B5867.tree = HexagonCover.NBand.M8300_8500.SplitData.node5867 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5868

def B5866 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556321586118343740978060776866032648256] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B5867, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq5866 : B5866.tree = HexagonCover.NBand.M8300_8500.SplitData.node5866 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5867
  · rfl

def B5846 : Block := .branch 113 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5845_5847, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B5866]
theorem treeEq5846 : B5846.tree = HexagonCover.NBand.M8300_8500.SplitData.node5846 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5866

def B5880 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5880 : B5880.tree = HexagonCover.NBand.M8300_8500.SplitData.node5880 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5879 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5880, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5879 : B5879.tree = HexagonCover.NBand.M8300_8500.SplitData.node5879 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5880
  · rfl

def B5878 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B5879]
theorem treeEq5878 : B5878.tree = HexagonCover.NBand.M8300_8500.SplitData.node5878 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5879

def B5877 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B5878, (.leaf 0 [] 0)]
theorem treeEq5877 : B5877.tree = HexagonCover.NBand.M8300_8500.SplitData.node5877 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5878
  · rfl

def B5876 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B5877, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5876 : B5876.tree = HexagonCover.NBand.M8300_8500.SplitData.node5876 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5877
  · rfl

def B5845 : Block := .branch 108 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B5846, B5876, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1053).pointIds 1053)]
theorem treeEq5845 : B5845.tree = HexagonCover.NBand.M8300_8500.SplitData.node5845 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5846
  · exact treeEq5876
  · rfl
  · rfl

theorem accepted5845 : B5845.accepted = true := by decide +kernel
theorem checked5845 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5845 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5845]
  exact B5845.sound accepted5845
#print axioms checked5845

def Tip5843_5845 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5845 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked5845
def B5890 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq5890 : B5890.tree = HexagonCover.NBand.M8300_8500.SplitData.node5890 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5889 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B5890, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5889 : B5889.tree = HexagonCover.NBand.M8300_8500.SplitData.node5889 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5890
  · rfl
  · rfl

def B5888 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B5889, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5888 : B5888.tree = HexagonCover.NBand.M8300_8500.SplitData.node5888 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5889
  · rfl
  · rfl

def B5887 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B5888, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5887 : B5887.tree = HexagonCover.NBand.M8300_8500.SplitData.node5887 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5888
  · rfl
  · rfl

def B5886 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5887, (.leaf 0 [] 0)]
theorem treeEq5886 : B5886.tree = HexagonCover.NBand.M8300_8500.SplitData.node5886 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5887
  · rfl

def B5885 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5886, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5885 : B5885.tree = HexagonCover.NBand.M8300_8500.SplitData.node5885 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5886
  · rfl

def B5884 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B5885, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5884 : B5884.tree = HexagonCover.NBand.M8300_8500.SplitData.node5884 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5885
  · rfl
  · rfl

def B5883 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 14507109835375550096498696, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5884, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq5883 : B5883.tree = HexagonCover.NBand.M8300_8500.SplitData.node5883 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5884
  · rfl
  · rfl
  · rfl

def B5882 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 43556142965880123323311949751266331459616, 3367299772432183711937480706503691896793189324423232] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B5883]
theorem treeEq5882 : B5882.tree = HexagonCover.NBand.M8300_8500.SplitData.node5882 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5883

def B5881 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311202792277271551033117370077413440] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B5882, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq5881 : B5881.tree = HexagonCover.NBand.M8300_8500.SplitData.node5881 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5882
  · rfl

def B5844 : Block := .branch 100 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5843_5845, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B5881]
theorem treeEq5844 : B5844.tree = HexagonCover.NBand.M8300_8500.SplitData.node5844 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5881

def B5895 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5895 : B5895.tree = HexagonCover.NBand.M8300_8500.SplitData.node5895 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5894 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5895, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5894 : B5894.tree = HexagonCover.NBand.M8300_8500.SplitData.node5894 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5895
  · rfl

def B5893 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B5894]
theorem treeEq5893 : B5893.tree = HexagonCover.NBand.M8300_8500.SplitData.node5893 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5894

def B5892 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B5893, (.leaf 0 [] 0)]
theorem treeEq5892 : B5892.tree = HexagonCover.NBand.M8300_8500.SplitData.node5892 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5893
  · rfl

def B5891 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B5892, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5891 : B5891.tree = HexagonCover.NBand.M8300_8500.SplitData.node5891 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5892
  · rfl

def B5843 : Block := .branch 98 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B5844, B5891, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq5843 : B5843.tree = HexagonCover.NBand.M8300_8500.SplitData.node5843 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5844
  · exact treeEq5891
  · rfl
  · rfl

theorem accepted5843 : B5843.accepted = true := by decide +kernel
theorem checked5843 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5843 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5843]
  exact B5843.sound accepted5843
#print axioms checked5843

end HexagonCover.NBand.M8300_8500.SplitTree.Run0080
