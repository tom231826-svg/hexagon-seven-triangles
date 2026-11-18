import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0012
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0013
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0989_0991 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0991 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0012.checked0991
def B1019 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M8300_8500.SplitData.node1019 := by
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

def B1018 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B1019, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M8300_8500.SplitData.node1018 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1019
  · rfl
  · rfl

def B1017 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B1018, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M8300_8500.SplitData.node1017 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1018
  · rfl
  · rfl

def B1016 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B1017, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M8300_8500.SplitData.node1016 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1017
  · rfl
  · rfl

def B1015 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1016, (.leaf 0 [] 0)]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M8300_8500.SplitData.node1015 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1016
  · rfl

def B1014 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1015, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M8300_8500.SplitData.node1014 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1015
  · rfl

def B1013 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B1014, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1013 : B1013.tree = HexagonCover.NBand.M8300_8500.SplitData.node1013 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1014
  · rfl
  · rfl

def B1012 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), B1013, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1012 : B1012.tree = HexagonCover.NBand.M8300_8500.SplitData.node1012 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1013
  · rfl
  · rfl
  · rfl

def B1011 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1012]
theorem treeEq1011 : B1011.tree = HexagonCover.NBand.M8300_8500.SplitData.node1011 := by
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
  · exact treeEq1012

def B1010 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1011, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1010 : B1010.tree = HexagonCover.NBand.M8300_8500.SplitData.node1010 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1011
  · rfl

def B0990 : Block := .branch 113 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0989_0991, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B1010]
theorem treeEq0990 : B0990.tree = HexagonCover.NBand.M8300_8500.SplitData.node0990 := by
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
  · exact treeEq1010

def B1024 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1024 : B1024.tree = HexagonCover.NBand.M8300_8500.SplitData.node1024 := by
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

def B1023 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1024, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1023 : B1023.tree = HexagonCover.NBand.M8300_8500.SplitData.node1023 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1024
  · rfl

def B1022 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B1023]
theorem treeEq1022 : B1022.tree = HexagonCover.NBand.M8300_8500.SplitData.node1022 := by
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
  · exact treeEq1023

def B1021 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B1022, (.leaf 0 [] 0)]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M8300_8500.SplitData.node1021 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1022
  · rfl

def B1020 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B1021, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M8300_8500.SplitData.node1020 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1021
  · rfl

def B0989 : Block := .branch 108 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0990, B1020, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0989 : B0989.tree = HexagonCover.NBand.M8300_8500.SplitData.node0989 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0990
  · exact treeEq1020
  · rfl
  · rfl

theorem accepted0989 : B0989.accepted = true := by decide +kernel
theorem checked0989 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0989 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0989]
  exact B0989.sound accepted0989
#print axioms checked0989

def Tip0987_0989 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0989 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked0989
def B1034 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq1034 : B1034.tree = HexagonCover.NBand.M8300_8500.SplitData.node1034 := by
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

def B1033 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B1034, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1033 : B1033.tree = HexagonCover.NBand.M8300_8500.SplitData.node1033 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1034
  · rfl
  · rfl

def B1032 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B1033, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1032 : B1032.tree = HexagonCover.NBand.M8300_8500.SplitData.node1032 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1033
  · rfl
  · rfl

def B1031 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B1032, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1031 : B1031.tree = HexagonCover.NBand.M8300_8500.SplitData.node1031 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1032
  · rfl
  · rfl

def B1030 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1031, (.leaf 0 [] 0)]
theorem treeEq1030 : B1030.tree = HexagonCover.NBand.M8300_8500.SplitData.node1030 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1031
  · rfl

def B1029 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1030, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1029 : B1029.tree = HexagonCover.NBand.M8300_8500.SplitData.node1029 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1030
  · rfl

def B1028 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B1029, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1028 : B1028.tree = HexagonCover.NBand.M8300_8500.SplitData.node1028 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1029
  · rfl
  · rfl

def B1027 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), B1028, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1027 : B1027.tree = HexagonCover.NBand.M8300_8500.SplitData.node1027 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1028
  · rfl
  · rfl
  · rfl

def B1026 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B1027]
theorem treeEq1026 : B1026.tree = HexagonCover.NBand.M8300_8500.SplitData.node1026 := by
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
  · exact treeEq1027

def B1025 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B1026, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1025 : B1025.tree = HexagonCover.NBand.M8300_8500.SplitData.node1025 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1026
  · rfl

def B0988 : Block := .branch 100 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0987_0989, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B1025]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M8300_8500.SplitData.node0988 := by
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
  · exact treeEq1025

def B1039 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1039 : B1039.tree = HexagonCover.NBand.M8300_8500.SplitData.node1039 := by
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

def B1038 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1039, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1038 : B1038.tree = HexagonCover.NBand.M8300_8500.SplitData.node1038 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1039
  · rfl

def B1037 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B1038]
theorem treeEq1037 : B1037.tree = HexagonCover.NBand.M8300_8500.SplitData.node1037 := by
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
  · exact treeEq1038

def B1036 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B1037, (.leaf 0 [] 0)]
theorem treeEq1036 : B1036.tree = HexagonCover.NBand.M8300_8500.SplitData.node1036 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1037
  · rfl

def B1035 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B1036, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1035 : B1035.tree = HexagonCover.NBand.M8300_8500.SplitData.node1035 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1036
  · rfl

def B0987 : Block := .branch 98 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0988, B1035, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M8300_8500.SplitData.node0987 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0988
  · exact treeEq1035
  · rfl
  · rfl

theorem accepted0987 : B0987.accepted = true := by decide +kernel
theorem checked0987 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0987 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0987]
  exact B0987.sound accepted0987
#print axioms checked0987

def Tip0984_0987 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0987 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked0987
def B1047 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq1047 : B1047.tree = HexagonCover.NBand.M8300_8500.SplitData.node1047 := by
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

def B1046 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B1047, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1046 : B1046.tree = HexagonCover.NBand.M8300_8500.SplitData.node1046 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1047
  · rfl
  · rfl

def B1045 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B1046, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq1045 : B1045.tree = HexagonCover.NBand.M8300_8500.SplitData.node1045 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1046
  · rfl
  · rfl

def B1044 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B1045, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq1044 : B1044.tree = HexagonCover.NBand.M8300_8500.SplitData.node1044 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1045
  · rfl
  · rfl

def B1043 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B1044, (.leaf 0 [] 0)]
theorem treeEq1043 : B1043.tree = HexagonCover.NBand.M8300_8500.SplitData.node1043 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1044
  · rfl

def B1042 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B1043, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1042 : B1042.tree = HexagonCover.NBand.M8300_8500.SplitData.node1042 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1043
  · rfl

def B1041 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B1042, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq1041 : B1041.tree = HexagonCover.NBand.M8300_8500.SplitData.node1041 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1042
  · rfl
  · rfl

def B1040 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), B1041, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq1040 : B1040.tree = HexagonCover.NBand.M8300_8500.SplitData.node1040 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1041
  · rfl
  · rfl
  · rfl

def B0986 : Block := .branch 90 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0984_0987, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B1040]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M8300_8500.SplitData.node0986 := by
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
  · exact treeEq1040

def B1050 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1050 : B1050.tree = HexagonCover.NBand.M8300_8500.SplitData.node1050 := by
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

def B1049 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1050, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1049 : B1049.tree = HexagonCover.NBand.M8300_8500.SplitData.node1049 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1050
  · rfl

def B1048 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79315205173276590894122819592, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 860).pointIds 860), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1049]
theorem treeEq1048 : B1048.tree = HexagonCover.NBand.M8300_8500.SplitData.node1048 := by
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
  · exact treeEq1049

def B0985 : Block := .branch 86 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0986, B1048, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M8300_8500.SplitData.node0985 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0986
  · exact treeEq1048
  · rfl
  · rfl
  · rfl

def B1053 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1053 : B1053.tree = HexagonCover.NBand.M8300_8500.SplitData.node1053 := by
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

def B1052 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1053, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1052 : B1052.tree = HexagonCover.NBand.M8300_8500.SplitData.node1052 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1053
  · rfl

def B1051 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 237732844575577597947620122632, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 861).pointIds 861), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1052]
theorem treeEq1051 : B1051.tree = HexagonCover.NBand.M8300_8500.SplitData.node1051 := by
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
  · exact treeEq1052

def B0984 : Block := .branch 85 ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B0985, B1051, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M8300_8500.SplitData.node0984 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0985
  · exact treeEq1051
  · rfl
  · rfl
  · rfl

theorem accepted0984 : B0984.accepted = true := by decide +kernel
theorem checked0984 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0984 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 4873482210321473860540420, 237694158949349929814029525000, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0984]
  exact B0984.sound accepted0984
#print axioms checked0984

def B1080 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M8300_8500.SplitData.node1080 := by
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

def B1079 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1080, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M8300_8500.SplitData.node1079 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1080
  · rfl

def B1078 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1079]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M8300_8500.SplitData.node1078 := by
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
  · exact treeEq1079

def B1085 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1085 : B1085.tree = HexagonCover.NBand.M8300_8500.SplitData.node1085 := by
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

def B1084 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1085, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1084 : B1084.tree = HexagonCover.NBand.M8300_8500.SplitData.node1084 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1085
  · rfl

def B1083 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1084]
theorem treeEq1083 : B1083.tree = HexagonCover.NBand.M8300_8500.SplitData.node1083 := by
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
  · exact treeEq1084

def B1082 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1083, (.leaf 0 [] 0)]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M8300_8500.SplitData.node1082 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1083
  · rfl

def B1081 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1082, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M8300_8500.SplitData.node1081 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1082
  · rfl

def B1077 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1078, B1081, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M8300_8500.SplitData.node1077 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1078
  · exact treeEq1081
  · rfl
  · rfl

def B1089 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M8300_8500.SplitData.node1089 := by
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

def B1088 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1089, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M8300_8500.SplitData.node1088 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1089
  · rfl

def B1087 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1088]
theorem treeEq1087 : B1087.tree = HexagonCover.NBand.M8300_8500.SplitData.node1087 := by
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
  · exact treeEq1088

def B1094 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq1094 : B1094.tree = HexagonCover.NBand.M8300_8500.SplitData.node1094 := by
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

def B1093 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B1094, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1093 : B1093.tree = HexagonCover.NBand.M8300_8500.SplitData.node1093 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1094
  · rfl

def B1092 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B1093]
theorem treeEq1092 : B1092.tree = HexagonCover.NBand.M8300_8500.SplitData.node1092 := by
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
  · exact treeEq1093

def B1091 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B1092, (.leaf 0 [] 0)]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M8300_8500.SplitData.node1091 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1092
  · rfl

def B1090 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B1091, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M8300_8500.SplitData.node1090 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1091
  · rfl

def B1086 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B1087, B1090, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1086 : B1086.tree = HexagonCover.NBand.M8300_8500.SplitData.node1086 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1087
  · exact treeEq1090
  · rfl
  · rfl

def B1076 : Block := .branch 115 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B1077, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B1086, (.leaf 0 [] 0)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M8300_8500.SplitData.node1076 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1077
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1086
  · rfl

theorem accepted1076 : B1076.accepted = true := by decide +kernel
theorem checked1076 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1076 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq1076]
  exact B1076.sound accepted1076
#print axioms checked1076

end HexagonCover.NBand.M8300_8500.SplitTree.Run0013
