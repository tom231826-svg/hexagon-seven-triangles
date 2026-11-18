import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0067
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B4876 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq4876 : B4876.tree = HexagonCover.NBand.M8300_8500.SplitData.node4876 := by
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

def B4875 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4876, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4875 : B4875.tree = HexagonCover.NBand.M8300_8500.SplitData.node4875 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4876
  · rfl
  · rfl

def B4874 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4875, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4874 : B4874.tree = HexagonCover.NBand.M8300_8500.SplitData.node4874 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4875
  · rfl
  · rfl

def B4873 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4874, (.leaf 0 [] 0)]
theorem treeEq4873 : B4873.tree = HexagonCover.NBand.M8300_8500.SplitData.node4873 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4874
  · rfl

def B4872 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4873, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4872 : B4872.tree = HexagonCover.NBand.M8300_8500.SplitData.node4872 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4873
  · rfl

def B4871 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4872, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4871 : B4871.tree = HexagonCover.NBand.M8300_8500.SplitData.node4871 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4872
  · rfl
  · rfl

def B4870 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4871, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4870 : B4870.tree = HexagonCover.NBand.M8300_8500.SplitData.node4870 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4871
  · rfl
  · rfl
  · rfl

def B4869 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 42535295865117307932921825928971419680, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B4870]
theorem treeEq4869 : B4869.tree = HexagonCover.NBand.M8300_8500.SplitData.node4869 := by
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
  · exact treeEq4870

def B4883 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4883 : B4883.tree = HexagonCover.NBand.M8300_8500.SplitData.node4883 := by
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

def B4882 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4883, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4882 : B4882.tree = HexagonCover.NBand.M8300_8500.SplitData.node4882 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4883
  · rfl
  · rfl

def B4881 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4882, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4881 : B4881.tree = HexagonCover.NBand.M8300_8500.SplitData.node4881 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4882
  · rfl
  · rfl

def B4880 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4881, (.leaf 0 [] 0)]
theorem treeEq4880 : B4880.tree = HexagonCover.NBand.M8300_8500.SplitData.node4880 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4881
  · rfl

def B4879 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4880, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4879 : B4879.tree = HexagonCover.NBand.M8300_8500.SplitData.node4879 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4880
  · rfl

def B4878 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4879, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4878 : B4878.tree = HexagonCover.NBand.M8300_8500.SplitData.node4878 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4879
  · rfl
  · rfl

def B4877 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4878, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4877 : B4877.tree = HexagonCover.NBand.M8300_8500.SplitData.node4877 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4878
  · rfl
  · rfl
  · rfl

def B4868 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4869, B4877]
theorem treeEq4868 : B4868.tree = HexagonCover.NBand.M8300_8500.SplitData.node4868 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4869
  · exact treeEq4877

theorem accepted4868 : B4868.accepted = true := by decide +kernel
theorem checked4868 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4868 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4868]
  exact B4868.sound accepted4868
#print axioms checked4868

def B4910 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq4910 : B4910.tree = HexagonCover.NBand.M8300_8500.SplitData.node4910 := by
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

def B4909 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4910, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4909 : B4909.tree = HexagonCover.NBand.M8300_8500.SplitData.node4909 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4910
  · rfl
  · rfl

def B4908 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4909, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4908 : B4908.tree = HexagonCover.NBand.M8300_8500.SplitData.node4908 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4909
  · rfl
  · rfl

def B4907 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4908, (.leaf 0 [] 0)]
theorem treeEq4907 : B4907.tree = HexagonCover.NBand.M8300_8500.SplitData.node4907 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4908
  · rfl

def B4906 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4907, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4906 : B4906.tree = HexagonCover.NBand.M8300_8500.SplitData.node4906 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4907
  · rfl

def B4905 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4906, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4905 : B4905.tree = HexagonCover.NBand.M8300_8500.SplitData.node4905 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4906
  · rfl
  · rfl

def B4904 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4905, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4904 : B4904.tree = HexagonCover.NBand.M8300_8500.SplitData.node4904 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4905
  · rfl
  · rfl
  · rfl

def B4903 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 42576834239985586553950069899605180448, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B4904]
theorem treeEq4903 : B4903.tree = HexagonCover.NBand.M8300_8500.SplitData.node4903 := by
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
  · exact treeEq4904

def B4917 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4917 : B4917.tree = HexagonCover.NBand.M8300_8500.SplitData.node4917 := by
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

def B4916 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4917, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4916 : B4916.tree = HexagonCover.NBand.M8300_8500.SplitData.node4916 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4917
  · rfl
  · rfl

def B4915 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4916, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4915 : B4915.tree = HexagonCover.NBand.M8300_8500.SplitData.node4915 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4916
  · rfl
  · rfl

def B4914 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B4915, (.leaf 0 [] 0)]
theorem treeEq4914 : B4914.tree = HexagonCover.NBand.M8300_8500.SplitData.node4914 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4915
  · rfl

def B4913 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B4914, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4913 : B4913.tree = HexagonCover.NBand.M8300_8500.SplitData.node4913 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4914
  · rfl

def B4912 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4913, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4912 : B4912.tree = HexagonCover.NBand.M8300_8500.SplitData.node4912 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4913
  · rfl
  · rfl

def B4911 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4912, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4911 : B4911.tree = HexagonCover.NBand.M8300_8500.SplitData.node4911 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4912
  · rfl
  · rfl
  · rfl

def B4902 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4903, B4911]
theorem treeEq4902 : B4902.tree = HexagonCover.NBand.M8300_8500.SplitData.node4902 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4903
  · exact treeEq4911

theorem accepted4902 : B4902.accepted = true := by decide +kernel
theorem checked4902 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4902 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4902]
  exact B4902.sound accepted4902
#print axioms checked4902

def Tip4900_4902 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4902 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] checked4902
def B4929 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq4929 : B4929.tree = HexagonCover.NBand.M8300_8500.SplitData.node4929 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4928 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4929, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq4928 : B4928.tree = HexagonCover.NBand.M8300_8500.SplitData.node4928 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4929
  · rfl
  · rfl

def B4927 : Block := .branch 166 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B4928, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq4927 : B4927.tree = HexagonCover.NBand.M8300_8500.SplitData.node4927 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4928
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4926 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B4927, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq4926 : B4926.tree = HexagonCover.NBand.M8300_8500.SplitData.node4926 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4927
  · rfl
  · rfl
  · rfl
  · rfl

def B4925 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4926, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4925 : B4925.tree = HexagonCover.NBand.M8300_8500.SplitData.node4925 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4926
  · rfl
  · rfl

def B4924 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4925, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4924 : B4924.tree = HexagonCover.NBand.M8300_8500.SplitData.node4924 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4925
  · rfl
  · rfl

def B4923 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4924, (.leaf 0 [] 0)]
theorem treeEq4923 : B4923.tree = HexagonCover.NBand.M8300_8500.SplitData.node4923 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4924
  · rfl

def B4922 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4923, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4922 : B4922.tree = HexagonCover.NBand.M8300_8500.SplitData.node4922 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4923
  · rfl

def B4921 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4922, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4921 : B4921.tree = HexagonCover.NBand.M8300_8500.SplitData.node4921 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4922
  · rfl
  · rfl

def B4920 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4921, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4920 : B4920.tree = HexagonCover.NBand.M8300_8500.SplitData.node4920 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4921
  · rfl
  · rfl
  · rfl

def B4919 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4920]
theorem treeEq4919 : B4919.tree = HexagonCover.NBand.M8300_8500.SplitData.node4919 := by
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
  · exact treeEq4920

def B4918 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4919, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4918 : B4918.tree = HexagonCover.NBand.M8300_8500.SplitData.node4918 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4919
  · rfl

def B4901 : Block := .branch 121 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip4900_4902, (.leaf 5 (Common.fact 256).pointIds 256), B4918]
theorem treeEq4901 : B4901.tree = HexagonCover.NBand.M8300_8500.SplitData.node4901 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4918

def B4934 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4934 : B4934.tree = HexagonCover.NBand.M8300_8500.SplitData.node4934 := by
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

def B4933 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4934, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4933 : B4933.tree = HexagonCover.NBand.M8300_8500.SplitData.node4933 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4934
  · rfl

def B4932 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4933]
theorem treeEq4932 : B4932.tree = HexagonCover.NBand.M8300_8500.SplitData.node4932 := by
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
  · exact treeEq4933

def B4931 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4932, (.leaf 0 [] 0)]
theorem treeEq4931 : B4931.tree = HexagonCover.NBand.M8300_8500.SplitData.node4931 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4932
  · rfl

def B4930 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4931, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4930 : B4930.tree = HexagonCover.NBand.M8300_8500.SplitData.node4930 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4931
  · rfl

def B4900 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4901, B4930, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq4900 : B4900.tree = HexagonCover.NBand.M8300_8500.SplitData.node4900 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4901
  · exact treeEq4930
  · rfl
  · rfl

theorem accepted4900 : B4900.accepted = true := by decide +kernel
theorem checked4900 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4900 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4900]
  exact B4900.sound accepted4900
#print axioms checked4900

def Tip4865_4868 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4868 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] checked4868
def Tip4865_4900 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4900 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] checked4900
def B4894 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 879).pointIds 879), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq4894 : B4894.tree = HexagonCover.NBand.M8300_8500.SplitData.node4894 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4893 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4894, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq4893 : B4893.tree = HexagonCover.NBand.M8300_8500.SplitData.node4893 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4894
  · rfl
  · rfl

def B4892 : Block := .branch 87 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89203661358856334443069799839808309560442896, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B4893, (.leaf 3 (Common.fact 877).pointIds 877), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 878).pointIds 878)]
theorem treeEq4892 : B4892.tree = HexagonCover.NBand.M8300_8500.SplitData.node4892 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4893
  · rfl
  · rfl
  · rfl
  · rfl

def B4891 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B4892, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4891 : B4891.tree = HexagonCover.NBand.M8300_8500.SplitData.node4891 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4892
  · rfl
  · rfl

def B4890 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794122492566142873090593446024019984, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B4891, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4890 : B4890.tree = HexagonCover.NBand.M8300_8500.SplitData.node4890 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4891
  · rfl
  · rfl

def B4889 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4890, (.leaf 0 [] 0)]
theorem treeEq4889 : B4889.tree = HexagonCover.NBand.M8300_8500.SplitData.node4889 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4890
  · rfl

def B4888 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202980794771529673459726544159758065172496, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4889, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4888 : B4888.tree = HexagonCover.NBand.M8300_8500.SplitData.node4888 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4889
  · rfl

def B4887 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B4888, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4887 : B4887.tree = HexagonCover.NBand.M8300_8500.SplitData.node4887 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4888
  · rfl
  · rfl

def B4886 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 649037107316853453566312041250832, 393248, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4887, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4886 : B4886.tree = HexagonCover.NBand.M8300_8500.SplitData.node4886 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4887
  · rfl
  · rfl
  · rfl

def B4885 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 649037107316853453566312041250832, 748288838313422294120286634350736906063837462396960, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B4886]
theorem treeEq4885 : B4885.tree = HexagonCover.NBand.M8300_8500.SplitData.node4885 := by
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
  · exact treeEq4886

def B4884 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393796575557201053662835845606834635374608, 393248, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4885, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4884 : B4884.tree = HexagonCover.NBand.M8300_8500.SplitData.node4884 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4885
  · rfl

def B4867 : Block := .branch 121 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), Tip4865_4868, (.leaf 5 (Common.fact 256).pointIds 256), B4884]
theorem treeEq4867 : B4867.tree = HexagonCover.NBand.M8300_8500.SplitData.node4867 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4884

def B4899 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4899 : B4899.tree = HexagonCover.NBand.M8300_8500.SplitData.node4899 := by
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

def B4898 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4899, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4898 : B4898.tree = HexagonCover.NBand.M8300_8500.SplitData.node4898 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4899
  · rfl

def B4897 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4898]
theorem treeEq4897 : B4897.tree = HexagonCover.NBand.M8300_8500.SplitData.node4897 := by
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
  · exact treeEq4898

def B4896 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4897, (.leaf 0 [] 0)]
theorem treeEq4896 : B4896.tree = HexagonCover.NBand.M8300_8500.SplitData.node4896 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4897
  · rfl

def B4895 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4896, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4895 : B4895.tree = HexagonCover.NBand.M8300_8500.SplitData.node4895 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4896
  · rfl

def B4866 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4867, B4895, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq4866 : B4866.tree = HexagonCover.NBand.M8300_8500.SplitData.node4866 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4867
  · exact treeEq4895
  · rfl
  · rfl

def B4865 : Block := .branch 115 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![B4866, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), Tip4865_4900, (.leaf 0 [] 0)]
theorem treeEq4865 : B4865.tree = HexagonCover.NBand.M8300_8500.SplitData.node4865 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4866
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4865 : B4865.accepted = true := by decide +kernel
theorem checked4865 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4865 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4865]
  exact B4865.sound accepted4865
#print axioms checked4865

end HexagonCover.NBand.M8300_8500.SplitTree.Run0067
