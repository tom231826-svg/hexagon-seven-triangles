import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0071
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0072
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip5206_5208 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5208 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396150483977878605001117425672, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0071.checked5208
def B5253 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq5253 : B5253.tree = HexagonCover.NBand.M8300_8500.SplitData.node5253 := by
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

def B5252 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B5253, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5252 : B5252.tree = HexagonCover.NBand.M8300_8500.SplitData.node5252 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5253
  · rfl
  · rfl

def B5251 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B5252, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5251 : B5251.tree = HexagonCover.NBand.M8300_8500.SplitData.node5251 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5252
  · rfl
  · rfl

def B5250 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B5251, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5250 : B5250.tree = HexagonCover.NBand.M8300_8500.SplitData.node5250 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5251
  · rfl
  · rfl

def B5249 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5250, (.leaf 0 [] 0)]
theorem treeEq5249 : B5249.tree = HexagonCover.NBand.M8300_8500.SplitData.node5249 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5250
  · rfl

def B5248 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5249, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5248 : B5248.tree = HexagonCover.NBand.M8300_8500.SplitData.node5248 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5249
  · rfl

def B5247 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B5248, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5247 : B5247.tree = HexagonCover.NBand.M8300_8500.SplitData.node5247 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5248
  · rfl
  · rfl

def B5246 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 9671406556917033397673992, 649037107316853453566312041250832, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5247, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq5246 : B5246.tree = HexagonCover.NBand.M8300_8500.SplitData.node5246 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5247
  · rfl
  · rfl
  · rfl

def B5245 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 43556142965880123323311949751266331459616, 3367299772432183711937480706503691896793189324423232] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B5246]
theorem treeEq5245 : B5245.tree = HexagonCover.NBand.M8300_8500.SplitData.node5245 := by
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
  · exact treeEq5246

def B5244 : Block := .branch 135 ![385, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311202792277271551033117370077413440] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B5245, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq5244 : B5244.tree = HexagonCover.NBand.M8300_8500.SplitData.node5244 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5245
  · rfl

def B5207 : Block := .branch 100 ![576460752303423873, 146437906389534210, 4740813226943354771460, 396150483977878605001117425672, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5206_5208, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B5244]
theorem treeEq5207 : B5207.tree = HexagonCover.NBand.M8300_8500.SplitData.node5207 := by
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
  · exact treeEq5244

def B5258 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5258 : B5258.tree = HexagonCover.NBand.M8300_8500.SplitData.node5258 := by
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

def B5257 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5258, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5257 : B5257.tree = HexagonCover.NBand.M8300_8500.SplitData.node5257 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5258
  · rfl

def B5256 : Block := .branch 163 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B5257]
theorem treeEq5256 : B5256.tree = HexagonCover.NBand.M8300_8500.SplitData.node5256 := by
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
  · exact treeEq5257

def B5255 : Block := .branch 165 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B5256, (.leaf 0 [] 0)]
theorem treeEq5255 : B5255.tree = HexagonCover.NBand.M8300_8500.SplitData.node5255 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5256
  · rfl

def B5254 : Block := .branch 167 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B5255, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5254 : B5254.tree = HexagonCover.NBand.M8300_8500.SplitData.node5254 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5255
  · rfl

def B5206 : Block := .branch 98 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B5207, B5254, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq5206 : B5206.tree = HexagonCover.NBand.M8300_8500.SplitData.node5206 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5207
  · exact treeEq5254
  · rfl
  · rfl

theorem accepted5206 : B5206.accepted = true := by decide +kernel
theorem checked5206 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5206 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5206]
  exact B5206.sound accepted5206
#print axioms checked5206

def Tip5203_5206 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node5206 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] checked5206
def B5266 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq5266 : B5266.tree = HexagonCover.NBand.M8300_8500.SplitData.node5266 := by
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

def B5265 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B5266, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq5265 : B5265.tree = HexagonCover.NBand.M8300_8500.SplitData.node5265 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5266
  · rfl
  · rfl

def B5264 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B5265, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5264 : B5264.tree = HexagonCover.NBand.M8300_8500.SplitData.node5264 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5265
  · rfl
  · rfl

def B5263 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B5264, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5263 : B5263.tree = HexagonCover.NBand.M8300_8500.SplitData.node5263 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5264
  · rfl
  · rfl

def B5262 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B5263, (.leaf 0 [] 0)]
theorem treeEq5262 : B5262.tree = HexagonCover.NBand.M8300_8500.SplitData.node5262 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5263
  · rfl

def B5261 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B5262, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5261 : B5261.tree = HexagonCover.NBand.M8300_8500.SplitData.node5261 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5262
  · rfl

def B5260 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B5261, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5260 : B5260.tree = HexagonCover.NBand.M8300_8500.SplitData.node5260 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5261
  · rfl
  · rfl

def B5259 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 9671406556917033397673992, 649037107316853453566312041250832, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5260, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq5259 : B5259.tree = HexagonCover.NBand.M8300_8500.SplitData.node5259 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5260
  · rfl
  · rfl
  · rfl

def B5205 : Block := .branch 90 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip5203_5206, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B5259]
theorem treeEq5205 : B5205.tree = HexagonCover.NBand.M8300_8500.SplitData.node5205 := by
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
  · exact treeEq5259

def B5269 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5269 : B5269.tree = HexagonCover.NBand.M8300_8500.SplitData.node5269 := by
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

def B5268 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5269, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5268 : B5268.tree = HexagonCover.NBand.M8300_8500.SplitData.node5268 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5269
  · rfl

def B5267 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79315205173276590894122819592, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 860).pointIds 860), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5268]
theorem treeEq5267 : B5267.tree = HexagonCover.NBand.M8300_8500.SplitData.node5267 := by
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
  · exact treeEq5268

def B5204 : Block := .branch 86 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79237833920821254626941624328, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B5205, B5267, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq5204 : B5204.tree = HexagonCover.NBand.M8300_8500.SplitData.node5204 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5205
  · exact treeEq5267
  · rfl
  · rfl
  · rfl

def B5272 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5272 : B5272.tree = HexagonCover.NBand.M8300_8500.SplitData.node5272 := by
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

def B5271 : Block := .branch 169 ![576460752303423873, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B5272, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq5271 : B5271.tree = HexagonCover.NBand.M8300_8500.SplitData.node5271 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5272
  · rfl

def B5270 : Block := .branch 170 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237732844575577597947620122632, 1393796574908163946345982392040522594222096, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B5271]
theorem treeEq5270 : B5270.tree = HexagonCover.NBand.M8300_8500.SplitData.node5270 := by
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
  · exact treeEq5271

def B5203 : Block := .branch 85 ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B5204, B5270, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq5203 : B5203.tree = HexagonCover.NBand.M8300_8500.SplitData.node5203 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5204
  · exact treeEq5270
  · rfl
  · rfl
  · rfl

theorem accepted5203 : B5203.accepted = true := by decide +kernel
theorem checked5203 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5203 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 237694158949349929814029525000, 1393796575557201053662835845606834635374608, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5203]
  exact B5203.sound accepted5203
#print axioms checked5203

def B5296 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq5296 : B5296.tree = HexagonCover.NBand.M8300_8500.SplitData.node5296 := by
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

def B5295 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B5296, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5295 : B5295.tree = HexagonCover.NBand.M8300_8500.SplitData.node5295 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5296
  · rfl
  · rfl

def B5294 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B5295, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5294 : B5294.tree = HexagonCover.NBand.M8300_8500.SplitData.node5294 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5295
  · rfl
  · rfl

def B5293 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5294, (.leaf 0 [] 0)]
theorem treeEq5293 : B5293.tree = HexagonCover.NBand.M8300_8500.SplitData.node5293 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5294
  · rfl

def B5292 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5293, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5292 : B5292.tree = HexagonCover.NBand.M8300_8500.SplitData.node5292 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5293
  · rfl

def B5291 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B5292, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5291 : B5291.tree = HexagonCover.NBand.M8300_8500.SplitData.node5291 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5292
  · rfl
  · rfl

def B5290 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5291, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq5290 : B5290.tree = HexagonCover.NBand.M8300_8500.SplitData.node5290 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5291
  · rfl
  · rfl
  · rfl

def B5289 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 42535295865117307932921825928971419680, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B5290]
theorem treeEq5289 : B5289.tree = HexagonCover.NBand.M8300_8500.SplitData.node5289 := by
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
  · exact treeEq5290

def B5303 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5303 : B5303.tree = HexagonCover.NBand.M8300_8500.SplitData.node5303 := by
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

def B5302 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B5303, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5302 : B5302.tree = HexagonCover.NBand.M8300_8500.SplitData.node5302 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5303
  · rfl
  · rfl

def B5301 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B5302, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5301 : B5301.tree = HexagonCover.NBand.M8300_8500.SplitData.node5301 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5302
  · rfl
  · rfl

def B5300 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5301, (.leaf 0 [] 0)]
theorem treeEq5300 : B5300.tree = HexagonCover.NBand.M8300_8500.SplitData.node5300 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5301
  · rfl

def B5299 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5300, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5299 : B5299.tree = HexagonCover.NBand.M8300_8500.SplitData.node5299 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5300
  · rfl

def B5298 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B5299, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5298 : B5298.tree = HexagonCover.NBand.M8300_8500.SplitData.node5298 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5299
  · rfl
  · rfl

def B5297 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5298, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5297 : B5297.tree = HexagonCover.NBand.M8300_8500.SplitData.node5297 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5298
  · rfl
  · rfl
  · rfl

def B5288 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B5289, B5297]
theorem treeEq5288 : B5288.tree = HexagonCover.NBand.M8300_8500.SplitData.node5288 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5289
  · exact treeEq5297

theorem accepted5288 : B5288.accepted = true := by decide +kernel
theorem checked5288 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5288 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5288]
  exact B5288.sound accepted5288
#print axioms checked5288

def B5330 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 623).pointIds 623)]
theorem treeEq5330 : B5330.tree = HexagonCover.NBand.M8300_8500.SplitData.node5330 := by
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

def B5329 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B5330, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5329 : B5329.tree = HexagonCover.NBand.M8300_8500.SplitData.node5329 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5330
  · rfl
  · rfl

def B5328 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B5329, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5328 : B5328.tree = HexagonCover.NBand.M8300_8500.SplitData.node5328 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5329
  · rfl
  · rfl

def B5327 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5328, (.leaf 0 [] 0)]
theorem treeEq5327 : B5327.tree = HexagonCover.NBand.M8300_8500.SplitData.node5327 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5328
  · rfl

def B5326 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5327, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5326 : B5326.tree = HexagonCover.NBand.M8300_8500.SplitData.node5326 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5327
  · rfl

def B5325 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B5326, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5325 : B5325.tree = HexagonCover.NBand.M8300_8500.SplitData.node5325 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5326
  · rfl
  · rfl

def B5324 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 4115588610745606006056499690254200573455530083221568] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5325, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq5324 : B5324.tree = HexagonCover.NBand.M8300_8500.SplitData.node5324 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5325
  · rfl
  · rfl
  · rfl

def B5323 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 42576834239985586553950069899605180448, 3367299772432183711936213055903463667391692621217856] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B5324]
theorem treeEq5323 : B5323.tree = HexagonCover.NBand.M8300_8500.SplitData.node5323 := by
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
  · exact treeEq5324

def B5337 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203664017961363120218399100988742162284560, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 876).pointIds 876), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq5337 : B5337.tree = HexagonCover.NBand.M8300_8500.SplitData.node5337 := by
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

def B5336 : Block := .branch 129 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 875).pointIds 875), B5337, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1064).pointIds 1064)]
theorem treeEq5336 : B5336.tree = HexagonCover.NBand.M8300_8500.SplitData.node5336 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5337
  · rfl
  · rfl

def B5335 : Block := .branch 138 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 874).pointIds 874), B5336, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq5335 : B5335.tree = HexagonCover.NBand.M8300_8500.SplitData.node5335 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5336
  · rfl
  · rfl

def B5334 : Block := .branch 165 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), B5335, (.leaf 0 [] 0)]
theorem treeEq5334 : B5334.tree = HexagonCover.NBand.M8300_8500.SplitData.node5334 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5335
  · rfl

def B5333 : Block := .branch 167 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 89202983453227521243291472351773878625861648, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B5334, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq5333 : B5333.tree = HexagonCover.NBand.M8300_8500.SplitData.node5333 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5334
  · rfl

def B5332 : Block := .branch 146 ![385, 1538, 6148, 1496577676626845252854571165995113542489721763029000, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 873).pointIds 873), B5333, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq5332 : B5332.tree = HexagonCover.NBand.M8300_8500.SplitData.node5332 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5333
  · rfl
  · rfl

def B5331 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 664613997897293639730362046839021576, 2659105028677148599261180432601939984, 393248, 3367299783582598846497389743979255725541802345234496] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B5332, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq5331 : B5331.tree = HexagonCover.NBand.M8300_8500.SplitData.node5331 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5332
  · rfl
  · rfl
  · rfl

def B5322 : Block := .branch 125 ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 1055).pointIds 1055), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B5323, B5331]
theorem treeEq5322 : B5322.tree = HexagonCover.NBand.M8300_8500.SplitData.node5322 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5323
  · exact treeEq5331

theorem accepted5322 : B5322.accepted = true := by decide +kernel
theorem checked5322 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node5322 (maskNeeds ![576460752303423873, 146437906389534210, 4740813226943354771460, 664614077125456153994699640382971912, 1393799234013192623494581653220955196063760, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq5322]
  exact B5322.sound accepted5322
#print axioms checked5322

end HexagonCover.NBand.M8300_8500.SplitTree.Run0072
