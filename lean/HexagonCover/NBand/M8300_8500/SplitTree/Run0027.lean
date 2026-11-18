import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0023
import HexagonCover.NBand.M8300_8500.SplitTree.Run0024
import HexagonCover.NBand.M8300_8500.SplitTree.Run0026
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0027
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip1997_1999 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1999 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] HexagonCover.NBand.M8300_8500.SplitTree.Run0026.checked1999
def B2027 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq2027 : B2027.tree = HexagonCover.NBand.M8300_8500.SplitData.node2027 := by
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

def B2026 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B2027, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2026 : B2026.tree = HexagonCover.NBand.M8300_8500.SplitData.node2026 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2027
  · rfl
  · rfl

def B2025 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B2026, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2025 : B2025.tree = HexagonCover.NBand.M8300_8500.SplitData.node2025 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2026
  · rfl
  · rfl

def B2024 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B2025, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2024 : B2024.tree = HexagonCover.NBand.M8300_8500.SplitData.node2024 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2025
  · rfl
  · rfl

def B2023 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2024, (.leaf 0 [] 0)]
theorem treeEq2023 : B2023.tree = HexagonCover.NBand.M8300_8500.SplitData.node2023 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2024
  · rfl

def B2022 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2023, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2022 : B2022.tree = HexagonCover.NBand.M8300_8500.SplitData.node2022 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2023
  · rfl

def B2021 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B2022, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2021 : B2021.tree = HexagonCover.NBand.M8300_8500.SplitData.node2021 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2022
  · rfl
  · rfl

def B2020 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 14507109835375550096498696, 178405961588894022239602599634753204089094160, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B2021, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq2020 : B2020.tree = HexagonCover.NBand.M8300_8500.SplitData.node2020 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2021
  · rfl
  · rfl
  · rfl

def B2019 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2020]
theorem treeEq2019 : B2019.tree = HexagonCover.NBand.M8300_8500.SplitData.node2019 := by
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
  · exact treeEq2020

def B2018 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2019, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq2018 : B2018.tree = HexagonCover.NBand.M8300_8500.SplitData.node2018 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2019
  · rfl

def B1998 : Block := .branch 113 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1997_1999, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B2018]
theorem treeEq1998 : B1998.tree = HexagonCover.NBand.M8300_8500.SplitData.node1998 := by
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
  · exact treeEq2018

def B2032 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2032 : B2032.tree = HexagonCover.NBand.M8300_8500.SplitData.node2032 := by
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

def B2031 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2032, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2031 : B2031.tree = HexagonCover.NBand.M8300_8500.SplitData.node2031 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2032
  · rfl

def B2030 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B2031]
theorem treeEq2030 : B2030.tree = HexagonCover.NBand.M8300_8500.SplitData.node2030 := by
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
  · exact treeEq2031

def B2029 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B2030, (.leaf 0 [] 0)]
theorem treeEq2029 : B2029.tree = HexagonCover.NBand.M8300_8500.SplitData.node2029 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2030
  · rfl

def B2028 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B2029, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2028 : B2028.tree = HexagonCover.NBand.M8300_8500.SplitData.node2028 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2029
  · rfl

def B1997 : Block := .branch 108 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B1998, B2028, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1997 : B1997.tree = HexagonCover.NBand.M8300_8500.SplitData.node1997 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1998
  · exact treeEq2028
  · rfl
  · rfl

theorem accepted1997 : B1997.accepted = true := by decide +kernel
theorem checked1997 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1997 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1997]
  exact B1997.sound accepted1997
#print axioms checked1997

def Tip1995_1997 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1997 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1997
def B2042 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq2042 : B2042.tree = HexagonCover.NBand.M8300_8500.SplitData.node2042 := by
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

def B2041 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B2042, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2041 : B2041.tree = HexagonCover.NBand.M8300_8500.SplitData.node2041 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2042
  · rfl
  · rfl

def B2040 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B2041, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2040 : B2040.tree = HexagonCover.NBand.M8300_8500.SplitData.node2040 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2041
  · rfl
  · rfl

def B2039 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B2040, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2039 : B2039.tree = HexagonCover.NBand.M8300_8500.SplitData.node2039 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2040
  · rfl
  · rfl

def B2038 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2039, (.leaf 0 [] 0)]
theorem treeEq2038 : B2038.tree = HexagonCover.NBand.M8300_8500.SplitData.node2038 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2039
  · rfl

def B2037 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2038, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2037 : B2037.tree = HexagonCover.NBand.M8300_8500.SplitData.node2037 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2038
  · rfl

def B2036 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B2037, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2036 : B2036.tree = HexagonCover.NBand.M8300_8500.SplitData.node2036 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2037
  · rfl
  · rfl

def B2035 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 14507109835375550096498696, 178405961588894022239602599634753204089094160, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B2036, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2035 : B2035.tree = HexagonCover.NBand.M8300_8500.SplitData.node2035 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2036
  · rfl
  · rfl
  · rfl

def B2034 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B2035]
theorem treeEq2034 : B2034.tree = HexagonCover.NBand.M8300_8500.SplitData.node2034 := by
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
  · exact treeEq2035

def B2033 : Block := .branch 135 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B2034, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2033 : B2033.tree = HexagonCover.NBand.M8300_8500.SplitData.node2033 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2034
  · rfl

def B1996 : Block := .branch 100 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 396155319681157063517816250376, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1995_1997, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B2033]
theorem treeEq1996 : B1996.tree = HexagonCover.NBand.M8300_8500.SplitData.node1996 := by
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
  · exact treeEq2033

def B2047 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq2047 : B2047.tree = HexagonCover.NBand.M8300_8500.SplitData.node2047 := by
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

def B2046 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2047, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2046 : B2046.tree = HexagonCover.NBand.M8300_8500.SplitData.node2046 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2047
  · rfl

def B2045 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B2046]
theorem treeEq2045 : B2045.tree = HexagonCover.NBand.M8300_8500.SplitData.node2045 := by
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
  · exact treeEq2046

def B2044 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B2045, (.leaf 0 [] 0)]
theorem treeEq2044 : B2044.tree = HexagonCover.NBand.M8300_8500.SplitData.node2044 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2045
  · rfl

def B2043 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B2044, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2043 : B2043.tree = HexagonCover.NBand.M8300_8500.SplitData.node2043 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2044
  · rfl

def B1995 : Block := .branch 98 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B1996, B2043, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq1995 : B1995.tree = HexagonCover.NBand.M8300_8500.SplitData.node1995 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1996
  · exact treeEq2043
  · rfl
  · rfl

theorem accepted1995 : B1995.accepted = true := by decide +kernel
theorem checked1995 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1995 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1995]
  exact B1995.sound accepted1995
#print axioms checked1995

def Tip1992_1995 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1995 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1995
def B2055 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq2055 : B2055.tree = HexagonCover.NBand.M8300_8500.SplitData.node2055 := by
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

def B2054 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 899).pointIds 899), B2055, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq2054 : B2054.tree = HexagonCover.NBand.M8300_8500.SplitData.node2054 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2055
  · rfl
  · rfl

def B2053 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582556311201525864611362089096148273332288] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 898).pointIds 898), B2054, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq2053 : B2053.tree = HexagonCover.NBand.M8300_8500.SplitData.node2053 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2054
  · rfl
  · rfl

def B2052 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 897).pointIds 897), B2053, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq2052 : B2052.tree = HexagonCover.NBand.M8300_8500.SplitData.node2052 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2053
  · rfl
  · rfl

def B2051 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B2052, (.leaf 0 [] 0)]
theorem treeEq2051 : B2051.tree = HexagonCover.NBand.M8300_8500.SplitData.node2051 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2052
  · rfl

def B2050 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 89202980794771529673459726544159758065172496, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B2051, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2050 : B2050.tree = HexagonCover.NBand.M8300_8500.SplitData.node2050 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2051
  · rfl

def B2049 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573283208583647503225020506120, 649037107316853453566312041250832, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 896).pointIds 896), B2050, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq2049 : B2049.tree = HexagonCover.NBand.M8300_8500.SplitData.node2049 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2050
  · rfl
  · rfl

def B2048 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 14507109835375550096498696, 178405961588894022239602599634753204089094160, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), B2049, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq2048 : B2048.tree = HexagonCover.NBand.M8300_8500.SplitData.node2048 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2049
  · rfl
  · rfl
  · rfl

def B1994 : Block := .branch 90 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip1992_1995, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B2048]
theorem treeEq1994 : B1994.tree = HexagonCover.NBand.M8300_8500.SplitData.node1994 := by
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
  · exact treeEq2048

def B2058 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2058 : B2058.tree = HexagonCover.NBand.M8300_8500.SplitData.node2058 := by
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

def B2057 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2058, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2057 : B2057.tree = HexagonCover.NBand.M8300_8500.SplitData.node2057 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2058
  · rfl

def B2056 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79310369469998132377423994888, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2057]
theorem treeEq2056 : B2056.tree = HexagonCover.NBand.M8300_8500.SplitData.node2056 := by
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
  · exact treeEq2057

def B1993 : Block := .branch 86 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 79242669624099713143640449032, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B1994, B2056, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1993 : B1993.tree = HexagonCover.NBand.M8300_8500.SplitData.node1993 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1994
  · exact treeEq2056
  · rfl
  · rfl
  · rfl

def B2061 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2061 : B2061.tree = HexagonCover.NBand.M8300_8500.SplitData.node2061 := by
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

def B2060 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2061, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2060 : B2060.tree = HexagonCover.NBand.M8300_8500.SplitData.node2060 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2061
  · rfl

def B2059 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237728008872299139430921297928, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 893).pointIds 893), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2060]
theorem treeEq2059 : B2059.tree = HexagonCover.NBand.M8300_8500.SplitData.node2059 := by
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
  · exact treeEq2060

def B1992 : Block := .branch 85 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B1993, B2059, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq1992 : B1992.tree = HexagonCover.NBand.M8300_8500.SplitData.node1992 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1993
  · exact treeEq2059
  · rfl
  · rfl
  · rfl

theorem accepted1992 : B1992.accepted = true := by decide +kernel
theorem checked1992 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1992 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1992]
  exact B1992.sound accepted1992
#print axioms checked1992

def Tip1658_1661 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1661 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0023.checked1661
def Tip1658_1789 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1789 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0024.checked1789
def Tip1658_1864 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1864 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0026.checked1864
def Tip1658_1992 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node1992 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked1992
def B1787 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1787 : B1787.tree = HexagonCover.NBand.M8300_8500.SplitData.node1787 := by
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

def B1786 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1787, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1786 : B1786.tree = HexagonCover.NBand.M8300_8500.SplitData.node1786 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1787
  · rfl

def B1785 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1786]
theorem treeEq1785 : B1785.tree = HexagonCover.NBand.M8300_8500.SplitData.node1785 := by
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
  · exact treeEq1786

def B1660 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip1658_1661, B1785, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1660 : B1660.tree = HexagonCover.NBand.M8300_8500.SplitData.node1660 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1785
  · rfl
  · rfl
  · rfl

def B1861 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1861 : B1861.tree = HexagonCover.NBand.M8300_8500.SplitData.node1861 := by
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

def B1860 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1861, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1860 : B1860.tree = HexagonCover.NBand.M8300_8500.SplitData.node1860 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1861
  · rfl

def B1859 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1860]
theorem treeEq1859 : B1859.tree = HexagonCover.NBand.M8300_8500.SplitData.node1859 := by
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
  · exact treeEq1860

def B1788 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip1658_1789, B1859, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1788 : B1788.tree = HexagonCover.NBand.M8300_8500.SplitData.node1788 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1859
  · rfl
  · rfl
  · rfl

def B1659 : Block := .branch 83 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B1660, B1788, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq1659 : B1659.tree = HexagonCover.NBand.M8300_8500.SplitData.node1659 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1660
  · exact treeEq1788
  · rfl
  · rfl
  · rfl

def B1990 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq1990 : B1990.tree = HexagonCover.NBand.M8300_8500.SplitData.node1990 := by
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

def B1989 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B1990, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1989 : B1989.tree = HexagonCover.NBand.M8300_8500.SplitData.node1989 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1990
  · rfl

def B1988 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B1989]
theorem treeEq1988 : B1988.tree = HexagonCover.NBand.M8300_8500.SplitData.node1988 := by
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
  · exact treeEq1989

def B1863 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip1658_1864, B1988, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1863 : B1863.tree = HexagonCover.NBand.M8300_8500.SplitData.node1863 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1988
  · rfl
  · rfl
  · rfl

def B2064 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq2064 : B2064.tree = HexagonCover.NBand.M8300_8500.SplitData.node2064 := by
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

def B2063 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 79232998217542796110242799624, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 871).pointIds 871), (.leaf 4 (Common.fact 716).pointIds 716), B2064, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2063 : B2063.tree = HexagonCover.NBand.M8300_8500.SplitData.node2063 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2064
  · rfl

def B2062 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 37778931862957161715716, 237708666059185305364125999112, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 894).pointIds 894), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B2063]
theorem treeEq2062 : B2062.tree = HexagonCover.NBand.M8300_8500.SplitData.node2062 := by
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
  · exact treeEq2063

def B1991 : Block := .branch 84 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237698994652628388330728349704, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), Tip1658_1992, B2062, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1991 : B1991.tree = HexagonCover.NBand.M8300_8500.SplitData.node1991 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2062
  · rfl
  · rfl
  · rfl

def B1862 : Block := .branch 83 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), B1863, B1991, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq1862 : B1862.tree = HexagonCover.NBand.M8300_8500.SplitData.node1862 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1863
  · exact treeEq1991
  · rfl
  · rfl
  · rfl

def B1658 : Block := .branch 78 ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![B1659, B1862, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq1658 : B1658.tree = HexagonCover.NBand.M8300_8500.SplitData.node1658 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq1659
  · exact treeEq1862
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1658 : B1658.accepted = true := by decide +kernel
theorem checked1658 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node1658 (maskNeeds ![604463488519866704462209, 151152765055713897612802, 37778931862957161715716, 237689323246071471297330700296, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq1658]
  exact B1658.sound accepted1658
#print axioms checked1658

end HexagonCover.NBand.M8300_8500.SplitTree.Run0027
