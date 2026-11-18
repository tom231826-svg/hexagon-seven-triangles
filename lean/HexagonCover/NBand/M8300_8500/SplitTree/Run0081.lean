import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0080
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0081
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip5840_5843 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5843 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0080.checked5843
def B5903 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq5903 : B5903.tree = HexagonCover.NBand.M8300_8500.SplitData.node5903 := by
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

def B5902 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B5903, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5902 : B5902.tree = HexagonCover.NBand.M8300_8500.SplitData.node5902 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5903
  · rfl
  · rfl

def B5901 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B5902, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5901 : B5901.tree = HexagonCover.NBand.M8300_8500.SplitData.node5901 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5902
  · rfl
  · rfl

def B5900 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B5901, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5900 : B5900.tree = HexagonCover.NBand.M8300_8500.SplitData.node5900 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5901
  · rfl
  · rfl

def B5899 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5900, (.leaf 0 [] 0)]
theorem treeEq5899 : B5899.tree = HexagonCover.NBand.M8300_8500.SplitData.node5899 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5900
  · rfl

def B5898 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5899, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5898 : B5898.tree = HexagonCover.NBand.M8300_8500.SplitData.node5898 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5899
  · rfl

def B5897 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B5898, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5897 : B5897.tree = HexagonCover.NBand.M8300_8500.SplitData.node5897 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5898
  · rfl
  · rfl

def B5896 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 14507109835375550096498696, 649037107316853453566312041250832, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5897, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq5896 : B5896.tree = HexagonCover.NBand.M8300_8500.SplitData.node5896 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5897
  · rfl
  · rfl
  · rfl

def B5842 : Block := .branch 90 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5840_5843, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B5896]
theorem treeEq5842 : B5842.tree = HexagonCover.NBand.M8300_8500.SplitData.node5842 := by
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
  · exact treeEq5896

def B5906 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5906 : B5906.tree = HexagonCover.NBand.M8300_8500.SplitData.node5906 := by
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

def B5905 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5906, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5905 : B5905.tree = HexagonCover.NBand.M8300_8500.SplitData.node5905 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5906
  · rfl

def B5904 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79310369469998132377423994888, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5905]
theorem treeEq5904 : B5904.tree = HexagonCover.NBand.M8300_8500.SplitData.node5904 := by
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
  · exact treeEq5905

def B5841 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79242669624099713143640449032, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B5842, B5904, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq5841 : B5841.tree = HexagonCover.NBand.M8300_8500.SplitData.node5841 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5842
  · exact treeEq5904
  · rfl
  · rfl
  · rfl

def B5909 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5909 : B5909.tree = HexagonCover.NBand.M8300_8500.SplitData.node5909 := by
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

def B5908 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5909, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5908 : B5908.tree = HexagonCover.NBand.M8300_8500.SplitData.node5908 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5909
  · rfl

def B5907 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237728008872299139430921297928, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 893).pointIds 893), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5908]
theorem treeEq5907 : B5907.tree = HexagonCover.NBand.M8300_8500.SplitData.node5907 := by
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
  · exact treeEq5908

def B5840 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B5841, B5907, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq5840 : B5840.tree = HexagonCover.NBand.M8300_8500.SplitData.node5840 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5841
  · exact treeEq5907
  · rfl
  · rfl
  · rfl

theorem accepted5840 : B5840.accepted = true := by decide +kernel
theorem checked5840 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5840 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237698994652628388330728349704, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5840]
  exact B5840.sound accepted5840
#print axioms checked5840

def B5947 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5947 : B5947.tree = HexagonCover.NBand.M8300_8500.SplitData.node5947 := by
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

def B5946 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B5947, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq5946 : B5946.tree = HexagonCover.NBand.M8300_8500.SplitData.node5946 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5947
  · rfl
  · rfl

def B5945 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B5946, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq5945 : B5945.tree = HexagonCover.NBand.M8300_8500.SplitData.node5945 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5946
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5944 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B5945, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq5944 : B5944.tree = HexagonCover.NBand.M8300_8500.SplitData.node5944 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5945
  · rfl
  · rfl
  · rfl
  · rfl

def B5943 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366761032876207585342189208786669273120, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 574).pointIds 574), B5944]
theorem treeEq5943 : B5943.tree = HexagonCover.NBand.M8300_8500.SplitData.node5943 := by
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
  · exact treeEq5944

def B5942 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944466912589573234605283144949207269408, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5943, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq5942 : B5942.tree = HexagonCover.NBand.M8300_8500.SplitData.node5942 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5943
  · rfl

def B5941 : Block := .branch 138 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944466912589573234605283144949207269408, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B5942, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5941 : B5941.tree = HexagonCover.NBand.M8300_8500.SplitData.node5941 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5942
  · rfl
  · rfl

def B5940 : Block := .branch 165 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355573530071658587684226515959365894176, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5941, (.leaf 0 [] 0)]
theorem treeEq5940 : B5940.tree = HexagonCover.NBand.M8300_8500.SplitData.node5940 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5941
  · rfl

def B5939 : Block := .branch 167 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5940, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5939 : B5939.tree = HexagonCover.NBand.M8300_8500.SplitData.node5939 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5940
  · rfl

def B5938 : Block := .branch 146 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B5939, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5938 : B5938.tree = HexagonCover.NBand.M8300_8500.SplitData.node5938 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5939
  · rfl
  · rfl

def B5937 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5938, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5937 : B5937.tree = HexagonCover.NBand.M8300_8500.SplitData.node5937 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5938
  · rfl
  · rfl
  · rfl

theorem accepted5937 : B5937.accepted = true := by decide +kernel
theorem checked5937 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5937 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496]) := by
  rw [← treeEq5937]
  exact B5937.sound accepted5937
#print axioms checked5937

def Tip5926_5937 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5937 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582598846497389743979255725541802345234496] checked5937
def B5936 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650079819651154601222844760374944693583888, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 624).pointIds 624), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 551).pointIds 551)]
theorem treeEq5936 : B5936.tree = HexagonCover.NBand.M8300_8500.SplitData.node5936 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5935 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551432596305525122561114496217697233240080, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B5936, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq5935 : B5935.tree = HexagonCover.NBand.M8300_8500.SplitData.node5935 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5936
  · rfl
  · rfl

def B5934 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983452578484135974618898207566584709136, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B5935, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5934 : B5934.tree = HexagonCover.NBand.M8300_8500.SplitData.node5934 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5935
  · rfl
  · rfl

def B5933 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5934, (.leaf 0 [] 0)]
theorem treeEq5933 : B5933.tree = HexagonCover.NBand.M8300_8500.SplitData.node5933 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5934
  · rfl

def B5932 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5933, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5932 : B5932.tree = HexagonCover.NBand.M8300_8500.SplitData.node5932 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5933
  · rfl

def B5931 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B5932, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5931 : B5931.tree = HexagonCover.NBand.M8300_8500.SplitData.node5931 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5932
  · rfl
  · rfl

def B5930 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 577).pointIds 577), B5931, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq5930 : B5930.tree = HexagonCover.NBand.M8300_8500.SplitData.node5930 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5931
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5929 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B5930, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq5929 : B5929.tree = HexagonCover.NBand.M8300_8500.SplitData.node5929 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5930
  · rfl
  · rfl
  · rfl
  · rfl

def B5928 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5929, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq5928 : B5928.tree = HexagonCover.NBand.M8300_8500.SplitData.node5928 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5929
  · rfl
  · rfl
  · rfl

def B5927 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 42535295865117307932921825928971419680, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B5928]
theorem treeEq5927 : B5927.tree = HexagonCover.NBand.M8300_8500.SplitData.node5927 := by
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
  · exact treeEq5928

def B5926 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B5927, Tip5926_5937]
theorem treeEq5926 : B5926.tree = HexagonCover.NBand.M8300_8500.SplitData.node5926 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5927
  · rfl

theorem accepted5926 : B5926.accepted = true := by decide +kernel
theorem checked5926 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5926 (maskNeeds ![576460752303423873, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5926]
  exact B5926.sound accepted5926
#print axioms checked5926

def B5988 : Block := .branch 163 ![385, 1538, 6148, 24584, 2944046815350418332776618161041160161479196688, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 584).pointIds 584), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5988 : B5988.tree = HexagonCover.NBand.M8300_8500.SplitData.node5988 := by
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

def B5987 : Block := .branch 151 ![385, 1538, 6148, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B5988, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq5987 : B5987.tree = HexagonCover.NBand.M8300_8500.SplitData.node5987 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5988
  · rfl
  · rfl

def B5986 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 24584, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 577).pointIds 577), B5987, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 632).pointIds 632)]
theorem treeEq5986 : B5986.tree = HexagonCover.NBand.M8300_8500.SplitData.node5986 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5985 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 393248, 3367299783604371601068346665977420085189194389389376] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B5986, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq5985 : B5985.tree = HexagonCover.NBand.M8300_8500.SplitData.node5985 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5986
  · rfl
  · rfl
  · rfl
  · rfl

def B5984 : Block := .branch 166 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783604371601068346665977420085189194389389376] ![B5985, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq5984 : B5984.tree = HexagonCover.NBand.M8300_8500.SplitData.node5984 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq5985
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5983 : Block := .branch 135 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 89551429938498570660046222142169888713703440, 982129100286366802571251075863963217452757303033888, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 625).pointIds 625), B5984]
theorem treeEq5983 : B5983.tree = HexagonCover.NBand.M8300_8500.SplitData.node5983 := by
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
  · exact treeEq5984

def B5982 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90945226513406734606392204534210411307827216, 233840261972944508450964441513226311388919841030176, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5983, (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq5982 : B5982.tree = HexagonCover.NBand.M8300_8500.SplitData.node5982 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5983
  · rfl

def B5981 : Block := .branch 138 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596777369679693619805708936200280659296272, 233840261972944508450964441513226311388919841030176, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B5982, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5981 : B5981.tree = HexagonCover.NBand.M8300_8500.SplitData.node5981 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5982
  · rfl
  · rfl

def B5980 : Block := .branch 165 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 187072209578355615068446526866305254759929999654944, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5981, (.leaf 0 [] 0)]
theorem treeEq5980 : B5980.tree = HexagonCover.NBand.M8300_8500.SplitData.node5980 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5981
  · rfl

def B5979 : Block := .branch 167 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 90596780028135685189637454743814401219985424, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5980, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5979 : B5979.tree = HexagonCover.NBand.M8300_8500.SplitData.node5979 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5980
  · rfl

def B5978 : Block := .branch 146 ![385, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B5979, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5978 : B5978.tree = HexagonCover.NBand.M8300_8500.SplitData.node5978 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5979
  · rfl
  · rfl

def B5977 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5978, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5977 : B5977.tree = HexagonCover.NBand.M8300_8500.SplitData.node5977 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5978
  · rfl
  · rfl
  · rfl

theorem accepted5977 : B5977.accepted = true := by decide +kernel
theorem checked5977 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5977 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582598846497389743979255725541802345234496]) := by
  rw [← treeEq5977]
  exact B5977.sound accepted5977
#print axioms checked5977

def B6000 : Block := .branch 151 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 641).pointIds 641)]
theorem treeEq6000 : B6000.tree = HexagonCover.NBand.M8300_8500.SplitData.node6000 := by
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

def B5999 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6000, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq5999 : B5999.tree = HexagonCover.NBand.M8300_8500.SplitData.node5999 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6000
  · rfl
  · rfl

def B5998 : Block := .branch 166 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 748288838313422335658661502629357934307808096157728, 3367299783604331724228473118501232970977385979052096] ![B5999, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 638).pointIds 638), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq5998 : B5998.tree = HexagonCover.NBand.M8300_8500.SplitData.node5998 := by
  change Tree.branch (166 : Fin 177) _ = Tree.branch (166 : Fin 177) _
  apply congrArg (Tree.branch (166 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq5999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5997 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794122492566142873090593446024019984, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 570).pointIds 570), B5998, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5997 : B5997.tree = HexagonCover.NBand.M8300_8500.SplitData.node5997 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5998
  · rfl
  · rfl

def B5996 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5997, (.leaf 0 [] 0)]
theorem treeEq5996 : B5996.tree = HexagonCover.NBand.M8300_8500.SplitData.node5996 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5997
  · rfl

def B5995 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 89202980794771529673459726544159758065172496, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5996, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5995 : B5995.tree = HexagonCover.NBand.M8300_8500.SplitData.node5995 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5996
  · rfl

def B5994 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B5995, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5994 : B5994.tree = HexagonCover.NBand.M8300_8500.SplitData.node5994 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5995
  · rfl
  · rfl

def B5993 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 577).pointIds 577), B5994, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq5993 : B5993.tree = HexagonCover.NBand.M8300_8500.SplitData.node5993 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5994
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5992 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626845252854571161159410264031205064204296, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B5993, (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq5992 : B5992.tree = HexagonCover.NBand.M8300_8500.SplitData.node5992 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5993
  · rfl
  · rfl
  · rfl
  · rfl

def B5991 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783626115112623396319826380561081260265963584] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5992, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq5991 : B5991.tree = HexagonCover.NBand.M8300_8500.SplitData.node5991 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5992
  · rfl
  · rfl
  · rfl

def B5990 : Block := .branch 135 ![385, 146437906389534210, 4840444091685460053596164, 664613997892457936451903530140196872, 649037107316853453566312041250832, 748288838313422335658661502629357934307808096157728, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B5991]
theorem treeEq5990 : B5990.tree = HexagonCover.NBand.M8300_8500.SplitData.node5990 := by
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
  · exact treeEq5991

def B5989 : Block := .branch 169 ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582558969657516196503068611329993934897216] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5990, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq5989 : B5989.tree = HexagonCover.NBand.M8300_8500.SplitData.node5989 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5990
  · rfl

theorem accepted5989 : B5989.accepted = true := by decide +kernel
theorem checked5989 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5989 (maskNeeds ![385, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582558969657516196503068611329993934897216]) := by
  rw [← treeEq5989]
  exact B5989.sound accepted5989
#print axioms checked5989

end HexagonCover.NBand.M8300_8500.SplitTree.Run0081
