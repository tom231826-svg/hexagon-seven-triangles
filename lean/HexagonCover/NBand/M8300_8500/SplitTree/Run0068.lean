import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0067
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0068
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip4863_4865 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4865 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0067.checked4865
def B4945 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq4945 : B4945.tree = HexagonCover.NBand.M8300_8500.SplitData.node4945 := by
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
  · rfl

def B4944 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4945, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq4944 : B4944.tree = HexagonCover.NBand.M8300_8500.SplitData.node4944 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4945
  · rfl
  · rfl

def B4943 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B4944, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 884).pointIds 884)]
theorem treeEq4943 : B4943.tree = HexagonCover.NBand.M8300_8500.SplitData.node4943 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4944
  · rfl
  · rfl
  · rfl
  · rfl

def B4942 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B4943, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4942 : B4942.tree = HexagonCover.NBand.M8300_8500.SplitData.node4942 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4943
  · rfl
  · rfl

def B4941 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B4942, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4941 : B4941.tree = HexagonCover.NBand.M8300_8500.SplitData.node4941 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4942
  · rfl
  · rfl

def B4940 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4941, (.leaf 0 [] 0)]
theorem treeEq4940 : B4940.tree = HexagonCover.NBand.M8300_8500.SplitData.node4940 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4941
  · rfl

def B4939 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4940, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4939 : B4939.tree = HexagonCover.NBand.M8300_8500.SplitData.node4939 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4940
  · rfl

def B4938 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B4939, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4938 : B4938.tree = HexagonCover.NBand.M8300_8500.SplitData.node4938 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4939
  · rfl
  · rfl

def B4937 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 4835703278458516698849288, 649037107316853453566312041250832, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4938, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4937 : B4937.tree = HexagonCover.NBand.M8300_8500.SplitData.node4937 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4938
  · rfl
  · rfl
  · rfl

def B4936 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 43556142965880123323311949751266331459616, 3367299772432183722320806772973118924452685279658048] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4937]
theorem treeEq4936 : B4936.tree = HexagonCover.NBand.M8300_8500.SplitData.node4936 := by
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
  · exact treeEq4937

def B4935 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556321586118343740978060776866032648256] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4936, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq4935 : B4935.tree = HexagonCover.NBand.M8300_8500.SplitData.node4935 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4936
  · rfl

def B4864 : Block := .branch 113 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4863_4865, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B4935]
theorem treeEq4864 : B4864.tree = HexagonCover.NBand.M8300_8500.SplitData.node4864 := by
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
  · exact treeEq4935

def B4950 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4950 : B4950.tree = HexagonCover.NBand.M8300_8500.SplitData.node4950 := by
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

def B4949 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4950, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4949 : B4949.tree = HexagonCover.NBand.M8300_8500.SplitData.node4949 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4950
  · rfl

def B4948 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B4949]
theorem treeEq4948 : B4948.tree = HexagonCover.NBand.M8300_8500.SplitData.node4948 := by
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
  · exact treeEq4949

def B4947 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B4948, (.leaf 0 [] 0)]
theorem treeEq4947 : B4947.tree = HexagonCover.NBand.M8300_8500.SplitData.node4947 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4948
  · rfl

def B4946 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B4947, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4946 : B4946.tree = HexagonCover.NBand.M8300_8500.SplitData.node4946 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4947
  · rfl

def B4863 : Block := .branch 108 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B4864, B4946, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 1053).pointIds 1053)]
theorem treeEq4863 : B4863.tree = HexagonCover.NBand.M8300_8500.SplitData.node4863 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4864
  · exact treeEq4946
  · rfl
  · rfl

theorem accepted4863 : B4863.accepted = true := by decide +kernel
theorem checked4863 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4863 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4863]
  exact B4863.sound accepted4863
#print axioms checked4863

def Tip4861_4863 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4863 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked4863
def B4961 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq4961 : B4961.tree = HexagonCover.NBand.M8300_8500.SplitData.node4961 := by
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
  · rfl

def B4960 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4961, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq4960 : B4960.tree = HexagonCover.NBand.M8300_8500.SplitData.node4960 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4961
  · rfl
  · rfl

def B4959 : Block := .branch 87 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B4960, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq4959 : B4959.tree = HexagonCover.NBand.M8300_8500.SplitData.node4959 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4960
  · rfl
  · rfl
  · rfl
  · rfl

def B4958 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B4959, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4958 : B4958.tree = HexagonCover.NBand.M8300_8500.SplitData.node4958 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4959
  · rfl
  · rfl

def B4957 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B4958, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4957 : B4957.tree = HexagonCover.NBand.M8300_8500.SplitData.node4957 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4958
  · rfl
  · rfl

def B4956 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4957, (.leaf 0 [] 0)]
theorem treeEq4956 : B4956.tree = HexagonCover.NBand.M8300_8500.SplitData.node4956 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4957
  · rfl

def B4955 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4956, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4955 : B4955.tree = HexagonCover.NBand.M8300_8500.SplitData.node4955 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4956
  · rfl

def B4954 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B4955, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4954 : B4954.tree = HexagonCover.NBand.M8300_8500.SplitData.node4954 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4955
  · rfl
  · rfl

def B4953 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 4835703278458516698849288, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4954, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq4953 : B4953.tree = HexagonCover.NBand.M8300_8500.SplitData.node4953 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4954
  · rfl
  · rfl
  · rfl

def B4952 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 43556142965880123323311949751266331459616, 3367299772432183711937480706503691896793189324423232] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4953]
theorem treeEq4952 : B4952.tree = HexagonCover.NBand.M8300_8500.SplitData.node4952 := by
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
  · exact treeEq4953

def B4951 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311202792277271551033117370077413440] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4952, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4951 : B4951.tree = HexagonCover.NBand.M8300_8500.SplitData.node4951 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4952
  · rfl

def B4862 : Block := .branch 100 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4861_4863, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B4951]
theorem treeEq4862 : B4862.tree = HexagonCover.NBand.M8300_8500.SplitData.node4862 := by
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
  · exact treeEq4951

def B4966 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4966 : B4966.tree = HexagonCover.NBand.M8300_8500.SplitData.node4966 := by
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

def B4965 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4966, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4965 : B4965.tree = HexagonCover.NBand.M8300_8500.SplitData.node4965 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4966
  · rfl

def B4964 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B4965]
theorem treeEq4964 : B4964.tree = HexagonCover.NBand.M8300_8500.SplitData.node4964 := by
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
  · exact treeEq4965

def B4963 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B4964, (.leaf 0 [] 0)]
theorem treeEq4963 : B4963.tree = HexagonCover.NBand.M8300_8500.SplitData.node4963 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4964
  · rfl

def B4962 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B4963, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4962 : B4962.tree = HexagonCover.NBand.M8300_8500.SplitData.node4962 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4963
  · rfl

def B4861 : Block := .branch 98 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B4862, B4962, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq4861 : B4861.tree = HexagonCover.NBand.M8300_8500.SplitData.node4861 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4862
  · exact treeEq4962
  · rfl
  · rfl

theorem accepted4861 : B4861.accepted = true := by decide +kernel
theorem checked4861 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4861 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4861]
  exact B4861.sound accepted4861
#print axioms checked4861

def Tip4858_4861 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4861 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked4861
def B4975 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 891).pointIds 891)]
theorem treeEq4975 : B4975.tree = HexagonCover.NBand.M8300_8500.SplitData.node4975 := by
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

def B4974 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4975, (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq4974 : B4974.tree = HexagonCover.NBand.M8300_8500.SplitData.node4974 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4975
  · rfl

def B4973 : Block := .branch 87 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B4974, (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq4973 : B4973.tree = HexagonCover.NBand.M8300_8500.SplitData.node4973 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4974
  · rfl
  · rfl
  · rfl
  · rfl

def B4972 : Block := .branch 129 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B4973, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq4972 : B4972.tree = HexagonCover.NBand.M8300_8500.SplitData.node4972 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4973
  · rfl
  · rfl

def B4971 : Block := .branch 138 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B4972, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq4971 : B4971.tree = HexagonCover.NBand.M8300_8500.SplitData.node4971 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4972
  · rfl
  · rfl

def B4970 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4971, (.leaf 0 [] 0)]
theorem treeEq4970 : B4970.tree = HexagonCover.NBand.M8300_8500.SplitData.node4970 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4971
  · rfl

def B4969 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 90596777369679693619805708936200280659296272, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4970, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4969 : B4969.tree = HexagonCover.NBand.M8300_8500.SplitData.node4969 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4970
  · rfl

def B4968 : Block := .branch 146 ![576460752303423873, 146437906389534210, 4740813226943354771460, 1496577676626844588240652501699691354923785166807048, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B4969, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4968 : B4968.tree = HexagonCover.NBand.M8300_8500.SplitData.node4968 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4969
  · rfl
  · rfl

def B4967 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B4968, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq4967 : B4967.tree = HexagonCover.NBand.M8300_8500.SplitData.node4967 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4968
  · rfl
  · rfl
  · rfl

def B4860 : Block := .branch 90 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4858_4861, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B4967]
theorem treeEq4860 : B4860.tree = HexagonCover.NBand.M8300_8500.SplitData.node4860 := by
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
  · exact treeEq4967

def B4978 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4978 : B4978.tree = HexagonCover.NBand.M8300_8500.SplitData.node4978 := by
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

def B4977 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4978, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq4977 : B4977.tree = HexagonCover.NBand.M8300_8500.SplitData.node4977 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4978
  · rfl

def B4976 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79310369469998132377423994888, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B4977]
theorem treeEq4976 : B4976.tree = HexagonCover.NBand.M8300_8500.SplitData.node4976 := by
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
  · exact treeEq4977

def B4859 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79232998217542796110242799624, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4860, B4976, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq4859 : B4859.tree = HexagonCover.NBand.M8300_8500.SplitData.node4859 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4860
  · exact treeEq4976
  · rfl
  · rfl
  · rfl

def B4981 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4981 : B4981.tree = HexagonCover.NBand.M8300_8500.SplitData.node4981 := by
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

def B4980 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4981, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq4980 : B4980.tree = HexagonCover.NBand.M8300_8500.SplitData.node4980 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4981
  · rfl

def B4979 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237728008872299139430921297928, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 893).pointIds 893), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B4980]
theorem treeEq4979 : B4979.tree = HexagonCover.NBand.M8300_8500.SplitData.node4979 := by
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
  · exact treeEq4980

def B4858 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4859, B4979, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4858 : B4858.tree = HexagonCover.NBand.M8300_8500.SplitData.node4858 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4859
  · exact treeEq4979
  · rfl
  · rfl
  · rfl

theorem accepted4858 : B4858.accepted = true := by decide +kernel
theorem checked4858 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4858 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237689323246071471297330700296, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4858]
  exact B4858.sound accepted4858
#print axioms checked4858

def B4997 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4997 : B4997.tree = HexagonCover.NBand.M8300_8500.SplitData.node4997 := by
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

def B4996 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4997, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq4996 : B4996.tree = HexagonCover.NBand.M8300_8500.SplitData.node4996 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4997
  · rfl

def B4995 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614394047777617608967047956422664, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 895).pointIds 895), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B4996]
theorem treeEq4995 : B4995.tree = HexagonCover.NBand.M8300_8500.SplitData.node4995 := by
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
  · exact treeEq4996

def B5002 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5002 : B5002.tree = HexagonCover.NBand.M8300_8500.SplitData.node5002 := by
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

def B5001 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5002, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5001 : B5001.tree = HexagonCover.NBand.M8300_8500.SplitData.node5001 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5002
  · rfl

def B5000 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B5001]
theorem treeEq5000 : B5000.tree = HexagonCover.NBand.M8300_8500.SplitData.node5000 := by
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
  · exact treeEq5001

def B4999 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B5000, (.leaf 0 [] 0)]
theorem treeEq4999 : B4999.tree = HexagonCover.NBand.M8300_8500.SplitData.node4999 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5000
  · rfl

def B4998 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4999, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4998 : B4998.tree = HexagonCover.NBand.M8300_8500.SplitData.node4998 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4999
  · rfl

def B4994 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4995, B4998, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq4994 : B4994.tree = HexagonCover.NBand.M8300_8500.SplitData.node4994 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4995
  · exact treeEq4998
  · rfl
  · rfl

def B5006 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5006 : B5006.tree = HexagonCover.NBand.M8300_8500.SplitData.node5006 := by
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

def B5005 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5006, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5005 : B5005.tree = HexagonCover.NBand.M8300_8500.SplitData.node5005 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5006
  · rfl

def B5004 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614394047777617608967047956422664, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 895).pointIds 895), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5005]
theorem treeEq5004 : B5004.tree = HexagonCover.NBand.M8300_8500.SplitData.node5004 := by
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
  · exact treeEq5005

def B5011 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5011 : B5011.tree = HexagonCover.NBand.M8300_8500.SplitData.node5011 := by
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

def B5010 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5011, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5010 : B5010.tree = HexagonCover.NBand.M8300_8500.SplitData.node5010 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5011
  · rfl

def B5009 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B5010]
theorem treeEq5009 : B5009.tree = HexagonCover.NBand.M8300_8500.SplitData.node5009 := by
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
  · exact treeEq5010

def B5008 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B5009, (.leaf 0 [] 0)]
theorem treeEq5008 : B5008.tree = HexagonCover.NBand.M8300_8500.SplitData.node5008 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5009
  · rfl

def B5007 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B5008, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5007 : B5007.tree = HexagonCover.NBand.M8300_8500.SplitData.node5007 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5008
  · rfl

def B5003 : Block := .branch 119 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B5004, B5007, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5003 : B5003.tree = HexagonCover.NBand.M8300_8500.SplitData.node5003 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5004
  · exact treeEq5007
  · rfl
  · rfl

def B4993 : Block := .branch 115 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![B4994, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B5003, (.leaf 0 [] 0)]
theorem treeEq4993 : B4993.tree = HexagonCover.NBand.M8300_8500.SplitData.node4993 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4994
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5003
  · rfl

theorem accepted4993 : B4993.accepted = true := by decide +kernel
theorem checked4993 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4993 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 396155319681157063517816250376, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4993]
  exact B4993.sound accepted4993
#print axioms checked4993

end HexagonCover.NBand.M8300_8500.SplitTree.Run0068
