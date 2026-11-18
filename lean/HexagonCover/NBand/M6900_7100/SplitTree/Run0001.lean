import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0000
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0001
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0149_0166 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0166 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006723548183536335309995365386419956235657224, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] HexagonCover.NBand.M6900_7100.SplitTree.Run0000.checked0166
def B0186 : Block := .branch 170 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11324597171128832064061106935329246077354000, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 559).pointIds 559), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 569).pointIds 569), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0186 : B0186.tree = HexagonCover.NBand.M6900_7100.SplitData.node0186 := by
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
  · rfl

def B0165 : Block := .branch 137 ![5192298096474866913910771228344705, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), Tip0149_0166, B0186, (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M6900_7100.SplitData.node0165 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0186
  · rfl
  · rfl

def B0187 : Block := .branch 170 ![10384594955009694542441267557564801, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191056117155137180259998584029090152512] ![(.leaf 0 (Common.fact 571).pointIds 571), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 569).pointIds 569), (.leaf 4 (Common.fact 567).pointIds 567), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 572).pointIds 572)]
theorem treeEq0187 : B0187.tree = HexagonCover.NBand.M6900_7100.SplitData.node0187 := by
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
  · rfl

def B0164 : Block := .branch 112 ![10384594955009694542441267557564801, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![B0165, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0187]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M6900_7100.SplitData.node0164 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0165
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0187

def B0188 : Block := .branch 170 ![748288838313422304507415653225311531735138114208129, 1856910058928071511860315650, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191050924858278645432370053532760932416] ![(.leaf 0 (Common.fact 573).pointIds 573), (.leaf 1 (Common.fact 574).pointIds 574), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 569).pointIds 569), (.leaf 4 (Common.fact 567).pointIds 567), (.leaf 5 (Common.fact 548).pointIds 548), (.leaf 6 (Common.fact 549).pointIds 549)]
theorem treeEq0188 : B0188.tree = HexagonCover.NBand.M6900_7100.SplitData.node0188 := by
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
  · rfl

def B0163 : Block := .branch 90 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039735755165580962022322679603208, 11498821742992352557354354734334311401619472, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![B0164, B0188, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 532).pointIds 532)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M6900_7100.SplitData.node0163 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0164
  · exact treeEq0188
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0162 : Block := .branch 138 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B0163, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 531).pointIds 531)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M6900_7100.SplitData.node0162 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0163
  · rfl
  · rfl

def B0161 : Block := .branch 139 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0162, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 530).pointIds 530)]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M6900_7100.SplitData.node0161 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0162
  · rfl
  · rfl

def B0160 : Block := .branch 140 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0161, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 529).pointIds 529)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M6900_7100.SplitData.node0160 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0161
  · rfl
  · rfl

def B0159 : Block := .branch 141 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0160, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 528).pointIds 528)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M6900_7100.SplitData.node0159 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0160
  · rfl
  · rfl

def B0158 : Block := .branch 142 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549663894039814983328095226359916223553544, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0159, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 527).pointIds 527)]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M6900_7100.SplitData.node0158 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0159
  · rfl
  · rfl

def B0157 : Block := .branch 128 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419179191051249693744953916154187062957310016] ![(.leaf 0 (Common.fact 275).pointIds 275), (.leaf 1 (Common.fact 276).pointIds 276), (.leaf 2 (Common.fact 277).pointIds 277), B0158, (.leaf 4 (Common.fact 525).pointIds 525), (.leaf 5 (Common.fact 279).pointIds 279), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M6900_7100.SplitData.node0157 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0158
  · rfl
  · rfl
  · rfl

def B0156 : Block := .branch 129 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 311).pointIds 311), (.leaf 1 (Common.fact 312).pointIds 312), (.leaf 2 (Common.fact 313).pointIds 313), (.leaf 3 (Common.fact 314).pointIds 314), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 315).pointIds 315), B0157]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M6900_7100.SplitData.node0156 := by
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
  · exact treeEq0157

def B0155 : Block := .branch 130 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 518).pointIds 518), (.leaf 1 (Common.fact 519).pointIds 519), (.leaf 2 (Common.fact 520).pointIds 520), (.leaf 3 (Common.fact 521).pointIds 521), (.leaf 4 (Common.fact 522).pointIds 522), (.leaf 5 (Common.fact 523).pointIds 523), B0156]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M6900_7100.SplitData.node0155 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0156

def B0154 : Block := .branch 131 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 512).pointIds 512), (.leaf 1 (Common.fact 513).pointIds 513), (.leaf 2 (Common.fact 514).pointIds 514), (.leaf 3 (Common.fact 515).pointIds 515), (.leaf 4 (Common.fact 516).pointIds 516), (.leaf 5 (Common.fact 517).pointIds 517), B0155]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M6900_7100.SplitData.node0154 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0155

def B0153 : Block := .branch 132 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 221).pointIds 221), B0154]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M6900_7100.SplitData.node0153 := by
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
  · exact treeEq0154

def B0152 : Block := .branch 133 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 5846006549323611672894044864631851752484455342088, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 510).pointIds 510), (.leaf 5 (Common.fact 215).pointIds 215), B0153]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M6900_7100.SplitData.node0152 := by
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
  · exact treeEq0153

def B0151 : Block := .branch 162 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), B0152, (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 509).pointIds 509)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M6900_7100.SplitData.node0151 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl
  · rfl
  · rfl

def B0150 : Block := .branch 163 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 233840261972987002208454690542538204970878178295840, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 262).pointIds 262), B0151]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M6900_7100.SplitData.node0150 := by
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
  · exact treeEq0151

def B0149 : Block := .branch 165 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 187072209578398108825936775895617148341888336920608, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 506).pointIds 506), B0150, (.leaf 0 [] 0)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M6900_7100.SplitData.node0149 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0150
  · rfl

theorem accepted0149 : B0149.accepted = true := by decide +kernel
theorem checked0149 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0149 (maskNeeds ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 187072209578398108825936775895617148341888336920608, 374144419178510486515851868026989404972199420887104]) := by
  rw [← treeEq0149]
  exact B0149.sound accepted0149
#print axioms checked0149

def B0196 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0196 : B0196.tree = HexagonCover.NBand.M6900_7100.SplitData.node0196 := by
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

def B0195 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B0196, (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0195 : B0195.tree = HexagonCover.NBand.M6900_7100.SplitData.node0195 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0196
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0194 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 578).pointIds 578), B0195, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0194 : B0194.tree = HexagonCover.NBand.M6900_7100.SplitData.node0194 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0195
  · rfl
  · rfl
  · rfl
  · rfl

def B0193 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0194]
theorem treeEq0193 : B0193.tree = HexagonCover.NBand.M6900_7100.SplitData.node0193 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0194

def B0192 : Block := .branch 166 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 24584, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B0193, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0192 : B0192.tree = HexagonCover.NBand.M6900_7100.SplitData.node0192 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0193
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0191 : Block := .branch 151 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0192, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0191 : B0191.tree = HexagonCover.NBand.M6900_7100.SplitData.node0191 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0192
  · rfl

def B0200 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M6900_7100.SplitData.node0200 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0199 : Block := .branch 170 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 585).pointIds 585), (.leaf 1 (Common.fact 586).pointIds 586), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0200, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M6900_7100.SplitData.node0199 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0200
  · rfl
  · rfl

def B0198 : Block := .branch 124 ![748288838313422309699713749096305831648953460851073, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0199]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M6900_7100.SplitData.node0198 := by
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
  · exact treeEq0199

def B0204 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M6900_7100.SplitData.node0204 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0203 : Block := .branch 170 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 585).pointIds 585), (.leaf 1 (Common.fact 586).pointIds 586), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0204, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M6900_7100.SplitData.node0203 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0204
  · rfl
  · rfl

def B0202 : Block := .branch 159 ![748288838313443577347645069810233007181643047240065, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0203]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M6900_7100.SplitData.node0202 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203

def B0206 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0206 : B0206.tree = HexagonCover.NBand.M6900_7100.SplitData.node0206 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0205 : Block := .branch 170 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 585).pointIds 585), (.leaf 1 (Common.fact 586).pointIds 586), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0206, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M6900_7100.SplitData.node0205 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0206
  · rfl
  · rfl

def B0201 : Block := .branch 124 ![748288838313422309699712511156266546268678561726849, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0202, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0205]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M6900_7100.SplitData.node0201 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0202
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0205

def B0197 : Block := .branch 90 ![748288838313422309699712511156266546268678561726849, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0198, B0201, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M6900_7100.SplitData.node0197 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0198
  · exact treeEq0201
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0190 : Block := .branch 119 ![748288838313422309699712511156266546268678561726849, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0191, (.leaf 5 (Common.fact 163).pointIds 163), B0197]
theorem treeEq0190 : B0190.tree = HexagonCover.NBand.M6900_7100.SplitData.node0190 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0191
  · rfl
  · exact treeEq0197

def B0208 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0208 : B0208.tree = HexagonCover.NBand.M6900_7100.SplitData.node0208 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0207 : Block := .branch 170 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 585).pointIds 585), (.leaf 1 (Common.fact 586).pointIds 586), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0208, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0207 : B0207.tree = HexagonCover.NBand.M6900_7100.SplitData.node0207 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0208
  · rfl
  · rfl

def B0189 : Block := .branch 112 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0190, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0207]
theorem treeEq0189 : B0189.tree = HexagonCover.NBand.M6900_7100.SplitData.node0189 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0190
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0207

theorem accepted0189 : B0189.accepted = true := by decide +kernel
theorem checked0189 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0189 (maskNeeds ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0189]
  exact B0189.sound accepted0189
#print axioms checked0189

def B0220 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0220 : B0220.tree = HexagonCover.NBand.M6900_7100.SplitData.node0220 := by
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

def B0219 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B0220, (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq0219 : B0219.tree = HexagonCover.NBand.M6900_7100.SplitData.node0219 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0220
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0218 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 600).pointIds 600), B0219, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq0218 : B0218.tree = HexagonCover.NBand.M6900_7100.SplitData.node0218 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0219
  · rfl
  · rfl
  · rfl
  · rfl

def B0217 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 618970609938501595666843138, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B0218]
theorem treeEq0217 : B0217.tree = HexagonCover.NBand.M6900_7100.SplitData.node0217 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0218

def B0216 : Block := .branch 166 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 24584, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B0217, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0216 : B0216.tree = HexagonCover.NBand.M6900_7100.SplitData.node0216 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0217
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0215 : Block := .branch 151 ![5192296858534827628530496329220481, 618970609938501595666843138, 6148, 24584, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B0216, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq0215 : B0215.tree = HexagonCover.NBand.M6900_7100.SplitData.node0215 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0216
  · rfl

def B0224 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0224 : B0224.tree = HexagonCover.NBand.M6900_7100.SplitData.node0224 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0223 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 598).pointIds 598), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0224, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0223 : B0223.tree = HexagonCover.NBand.M6900_7100.SplitData.node0223 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0224
  · rfl
  · rfl

def B0222 : Block := .branch 124 ![748288838313422309699713749095715535838594755199361, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0223]
theorem treeEq0222 : B0222.tree = HexagonCover.NBand.M6900_7100.SplitData.node0222 := by
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
  · exact treeEq0223

def B0228 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M6900_7100.SplitData.node0228 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0227 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 598).pointIds 598), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0228, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M6900_7100.SplitData.node0227 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl
  · rfl

def B0226 : Block := .branch 159 ![748288838313443577347645069809642711371284341588353, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 602).pointIds 602), (.leaf 1 (Common.fact 601).pointIds 601), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B0227]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M6900_7100.SplitData.node0226 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0227

def B0230 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M6900_7100.SplitData.node0230 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0229 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 598).pointIds 598), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0230, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M6900_7100.SplitData.node0229 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0230
  · rfl
  · rfl

def B0225 : Block := .branch 124 ![748288838313422309699712511155676250458319856075137, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0226, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0229]
theorem treeEq0225 : B0225.tree = HexagonCover.NBand.M6900_7100.SplitData.node0225 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0226
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0229

def B0221 : Block := .branch 90 ![748288838313422309699712511155676250458319856075137, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B0222, B0225, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq0221 : B0221.tree = HexagonCover.NBand.M6900_7100.SplitData.node0221 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0222
  · exact treeEq0225
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0214 : Block := .branch 119 ![748288838313422309699712511155676250458319856075137, 618970609938501595666843138, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B0215, (.leaf 5 (Common.fact 163).pointIds 163), B0221]
theorem treeEq0214 : B0214.tree = HexagonCover.NBand.M6900_7100.SplitData.node0214 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0215
  · rfl
  · exact treeEq0221

def B0232 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 596).pointIds 596)]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M6900_7100.SplitData.node0232 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0231 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489224059899255257793515239357088792640] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 598).pointIds 598), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0232, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M6900_7100.SplitData.node0231 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0232
  · rfl
  · rfl

def B0213 : Block := .branch 112 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0214, (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), (.leaf 5 (Common.fact 537).pointIds 537), B0231]
theorem treeEq0213 : B0213.tree = HexagonCover.NBand.M6900_7100.SplitData.node0213 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0214
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231

theorem accepted0213 : B0213.accepted = true := by decide +kernel
theorem checked0213 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0213 (maskNeeds ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0213]
  exact B0213.sound accepted0213
#print axioms checked0213

def Tip0141_0149 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0149 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 187072209578398108825936775895617148341888336920608, 374144419178510486515851868026989404972199420887104] checked0149
def Tip0141_0189 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0189 ![748288838313422304507415652621438917738182232506753, 619574482552498551548544514, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked0189
def Tip0141_0213 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0213 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] checked0213
def B0148 : Block := .branch 167 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 11150372599265311570767859136324180753088528, 42535295865117307932921825928971419680, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 504).pointIds 504), Tip0141_0149, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M6900_7100.SplitData.node0148 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0147 : Block := .branch 143 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 98320, 42535295865117307932921825928971419680, 374144419178510486515851868026989404972199420887104] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), B0148, (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M6900_7100.SplitData.node0147 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0148
  · rfl
  · rfl

def B0146 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 618970019642691236961191426, 77919046967349146032132, 79305533766719673860725170184, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0147]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M6900_7100.SplitData.node0146 := by
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
  · exact treeEq0147

def B0145 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0146, Tip0141_0189, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M6900_7100.SplitData.node0145 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0146
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0212 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq0212 : B0212.tree = HexagonCover.NBand.M6900_7100.SplitData.node0212 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0211 : Block := .branch 170 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178510486515534955376932347621825245085760] ![(.leaf 0 (Common.fact 597).pointIds 597), (.leaf 1 (Common.fact 598).pointIds 598), (.leaf 2 (Common.fact 561).pointIds 561), (.leaf 3 (Common.fact 587).pointIds 587), B0212, (.leaf 5 (Common.fact 588).pointIds 588), (.leaf 6 (Common.fact 599).pointIds 599)]
theorem treeEq0211 : B0211.tree = HexagonCover.NBand.M6900_7100.SplitData.node0211 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0212
  · rfl
  · rfl

def B0210 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 618970609938501595666843138, 77919046967349146032132, 77371252455336267181219848, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B0211]
theorem treeEq0210 : B0210.tree = HexagonCover.NBand.M6900_7100.SplitData.node0210 := by
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
  · exact treeEq0211

def B0209 : Block := .branch 79 ![748288838313422304507415652620848621927823526855041, 618970609938501595666843138, 77919046967349146032132, 116056878683004400771817480, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0210, Tip0141_0213, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0209 : B0209.tree = HexagonCover.NBand.M6900_7100.SplitData.node0209 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0210
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0144 : Block := .branch 69 ![748288838313422304507415652620848621927823526855041, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![B0145, B0209, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M6900_7100.SplitData.node0144 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0145
  · exact treeEq0209
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0143 : Block := .branch 150 ![748288838313422304507415652620848621927823526855041, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 98320, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0144, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M6900_7100.SplitData.node0143 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0144
  · rfl
  · rfl

def B0142 : Block := .branch 125 ![748288838313422304507415652620848621927823526855041, 618970019642691236961191426, 77919046967349146032132, 79344219392947341994315767816, 98320, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 490).pointIds 490), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0143, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0142 : B0142.tree = HexagonCover.NBand.M6900_7100.SplitData.node0142 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0143
  · rfl

def B0141 : Block := .branch 169 ![10387129018270111715863986064851329, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B0142, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq0141 : B0141.tree = HexagonCover.NBand.M6900_7100.SplitData.node0141 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0142
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0141 : B0141.accepted = true := by decide +kernel
theorem checked0141 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0141 (maskNeeds ![10387129018270111715863986064851329, 618970020579439959454254594, 77937529740219874547716, 79344219392947341994315767816, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq0141]
  exact B0141.sound accepted0141
#print axioms checked0141

end HexagonCover.NBand.M6900_7100.SplitTree.Run0001
