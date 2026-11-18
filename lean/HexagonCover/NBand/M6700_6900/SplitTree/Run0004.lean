import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.NBand.M6700_6900.SplitTree.Run0000
import HexagonCover.NBand.M6700_6900.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0102_0112 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0112 ![1208926972536133781553537, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6700_6900.SplitTree.Run0003.checked0112
def B0110 : Block := .branch 101 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178491876999392325546342024890199475486784] ![(.leaf 0 (Common.fact 460).pointIds 460), (.leaf 1 (Common.fact 222).pointIds 222), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 461).pointIds 461)]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M6700_6900.SplitData.node0110 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0109 : Block := .branch 121 ![576460752303423873, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0110]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M6700_6900.SplitData.node0109 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0110

def B0108 : Block := .branch 150 ![576460752303423873, 1538, 6148, 24584, 98320, 42535295865117307932921825928971419680, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0109, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M6700_6900.SplitData.node0108 := by
  change Tree.branch (150 : Fin 175) _ = Tree.branch (150 : Fin 175) _
  apply congrArg (Tree.branch (150 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0109
  · rfl
  · rfl

def B0107 : Block := .branch 125 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 459).pointIds 459), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0108, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M6700_6900.SplitData.node0107 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0108
  · rfl

def B0106 : Block := .branch 164 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 458).pointIds 458), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0107]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M6700_6900.SplitData.node0106 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0107

def B0365 : Block := .branch 171 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 23945243539653359764829112828366565718790366975590416, 393248, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 883).pointIds 883), (.leaf 1 (Common.fact 884).pointIds 884), (.leaf 2 (Common.fact 885).pointIds 885), (.leaf 3 (Common.fact 798).pointIds 798), (.leaf 4 (Common.fact 799).pointIds 799), (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M6700_6900.SplitData.node0365 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0364 : Block := .branch 174 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1894836872821293704934334514670878877883008000983104] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 881).pointIds 881), (.leaf 3 (Common.fact 769).pointIds 769), B0365, (.leaf 5 (Common.fact 794).pointIds 794), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M6700_6900.SplitData.node0364 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl
  · rfl

def B0363 : Block := .branch 159 ![42535295865118516858741440558145732993, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1894106122002628253475232672254520736373180034711616] ![(.leaf 0 (Common.fact 877).pointIds 877), (.leaf 1 (Common.fact 878).pointIds 878), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0364]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M6700_6900.SplitData.node0363 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0364

def B0362 : Block := .branch 166 ![42535295865118516858741440558145732993, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 1894106122002628253475232672254520736373180034711616] ![B0363, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M6700_6900.SplitData.node0362 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0363
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0361 : Block := .branch 164 ![42535295865118516858741440558145732993, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0362]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M6700_6900.SplitData.node0361 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0362

def B0360 : Block := .branch 125 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0361, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M6700_6900.SplitData.node0360 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0361
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0359 : Block := .branch 143 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0360, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M6700_6900.SplitData.node0359 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0360
  · rfl

def B0358 : Block := .branch 173 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 875).pointIds 875), (.leaf 3 (Common.fact 782).pointIds 782), B0359, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M6700_6900.SplitData.node0358 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0359
  · rfl
  · rfl

def B0357 : Block := .branch 170 ![1208925819614629174706561, 1224980198156404226, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 871).pointIds 871), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 869).pointIds 869), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0358]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M6700_6900.SplitData.node0357 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0358

def B0111 : Block := .branch 60 ![1208925819614629174706561, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip0102_0112, B0357, (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), (.leaf 4 (Common.fact 289).pointIds 289), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M6700_6900.SplitData.node0111 := by
  change Tree.branch (60 : Fin 175) _ = Tree.branch (60 : Fin 175) _
  apply congrArg (Tree.branch (60 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0357
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0105 : Block := .branch 59 ![1208925819614629174706561, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0106, B0111, (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M6700_6900.SplitData.node0105 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0106
  · exact treeEq0111
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 80 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0105, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M6700_6900.SplitData.node0104 := by
  change Tree.branch (80 : Fin 175) _ = Tree.branch (80 : Fin 175) _
  apply congrArg (Tree.branch (80 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0105
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0103 : Block := .branch 92 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0104, (.leaf 1 (Common.fact 441).pointIds 441), (.leaf 2 (Common.fact 442).pointIds 442), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 444).pointIds 444), (.leaf 5 (Common.fact 445).pointIds 445), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M6700_6900.SplitData.node0103 := by
  change Tree.branch (92 : Fin 175) _ = Tree.branch (92 : Fin 175) _
  apply congrArg (Tree.branch (92 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0104
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0102 : Block := .branch 168 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 435).pointIds 435), (.leaf 1 (Common.fact 436).pointIds 436), (.leaf 2 (Common.fact 437).pointIds 437), (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), B0103]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M6700_6900.SplitData.node0102 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0103

theorem accepted0102 : B0102.accepted = true := by decide +kernel
theorem checked0102 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0102 (maskNeeds ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0102]
  exact B0102.sound accepted0102
#print axioms checked0102

def Tip0029_0048 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0048 ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] HexagonCover.NBand.M6700_6900.SplitTree.Run0000.checked0048
def Tip0029_0102 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0102 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0102
def B0047 : Block := .branch 107 ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 256).pointIds 256), (.leaf 1 (Common.fact 257).pointIds 257), (.leaf 2 (Common.fact 258).pointIds 258), Tip0029_0048, (.leaf 4 (Common.fact 259).pointIds 259), (.leaf 5 (Common.fact 260).pointIds 260), (.leaf 6 (Common.fact 261).pointIds 261)]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M6700_6900.SplitData.node0047 := by
  change Tree.branch (107 : Fin 175) _ = Tree.branch (107 : Fin 175) _
  apply congrArg (Tree.branch (107 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0046 : Block := .branch 118 ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), B0047, (.leaf 4 (Common.fact 253).pointIds 253), (.leaf 5 (Common.fact 254).pointIds 254), (.leaf 6 (Common.fact 255).pointIds 255)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M6700_6900.SplitData.node0046 := by
  change Tree.branch (118 : Fin 175) _ = Tree.branch (118 : Fin 175) _
  apply congrArg (Tree.branch (118 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0047
  · rfl
  · rfl
  · rfl

def B0045 : Block := .branch 128 ![288230376151712129, 302231526962350843233794, 6148, 174224571863599760141388291010792458838024, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), B0046, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M6700_6900.SplitData.node0045 := by
  change Tree.branch (128 : Fin 175) _ = Tree.branch (128 : Fin 175) _
  apply congrArg (Tree.branch (128 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0046
  · rfl
  · rfl
  · rfl

def B0044 : Block := .branch 137 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 2854517187409509478984797335390564511401902144] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), B0045, (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 0 [] 0)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M6700_6900.SplitData.node0044 := by
  change Tree.branch (137 : Fin 175) _ = Tree.branch (137 : Fin 175) _
  apply congrArg (Tree.branch (137 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0045
  · rfl
  · rfl
  · rfl

def B0043 : Block := .branch 151 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 11693440346339929305510536947699713652383843188752, 93536104789177786765035829293842113257979683143712, 21801997589716868225396491574238636408896] ![(.leaf 0 (Common.fact 233).pointIds 233), (.leaf 1 (Common.fact 234).pointIds 234), (.leaf 2 (Common.fact 235).pointIds 235), (.leaf 3 (Common.fact 236).pointIds 236), (.leaf 4 (Common.fact 237).pointIds 237), (.leaf 5 (Common.fact 238).pointIds 238), B0044]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M6700_6900.SplitData.node0043 := by
  change Tree.branch (151 : Fin 175) _ = Tree.branch (151 : Fin 175) _
  apply congrArg (Tree.branch (151 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0044

def B0042 : Block := .branch 163 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 93536104789177786765035829293842113257979683143712, 21801997589716868225396491574238636408896] ![(.leaf 0 (Common.fact 227).pointIds 227), (.leaf 1 (Common.fact 228).pointIds 228), (.leaf 2 (Common.fact 229).pointIds 229), (.leaf 3 (Common.fact 230).pointIds 230), B0043, (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 232).pointIds 232)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M6700_6900.SplitData.node0042 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0043
  · rfl
  · rfl

def B0041 : Block := .branch 101 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 93536104789177786765035829293842113257979683143712, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 221).pointIds 221), (.leaf 1 (Common.fact 222).pointIds 222), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), B0042]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M6700_6900.SplitData.node0041 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0042

def B0040 : Block := .branch 166 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21802002779478425559767661301741559218240] ![(.leaf 0 (Common.fact 215).pointIds 215), (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), B0041, (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M6700_6900.SplitData.node0040 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0041
  · rfl

def B0039 : Block := .branch 112 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 209).pointIds 209), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M6700_6900.SplitData.node0039 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0040

def B0038 : Block := .branch 65 ![288230376151712129, 302231526962350843233794, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), B0039, (.leaf 3 (Common.fact 136).pointIds 136), (.leaf 4 (Common.fact 137).pointIds 137), (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 208).pointIds 208)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M6700_6900.SplitData.node0038 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · rfl
  · rfl
  · rfl

def B0037 : Block := .branch 78 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 140).pointIds 140), B0038, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 207).pointIds 207)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M6700_6900.SplitData.node0037 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0038
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0036 : Block := .branch 138 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0037, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 206).pointIds 206)]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M6700_6900.SplitData.node0036 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037
  · rfl
  · rfl

def B0035 : Block := .branch 141 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21801997587181567024940032771245229998144] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0036, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 205).pointIds 205)]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M6700_6900.SplitData.node0035 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0036
  · rfl
  · rfl

def B0034 : Block := .branch 124 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21780729939249008370973571858280744484928] ![(.leaf 0 (Common.fact 199).pointIds 199), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 204).pointIds 204), B0035]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M6700_6900.SplitData.node0034 := by
  change Tree.branch (124 : Fin 175) _ = Tree.branch (124 : Fin 175) _
  apply congrArg (Tree.branch (124 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0035

def B0033 : Block := .branch 121 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0034]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M6700_6900.SplitData.node0033 := by
  change Tree.branch (121 : Fin 175) _ = Tree.branch (121 : Fin 175) _
  apply congrArg (Tree.branch (121 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0034

def B0032 : Block := .branch 150 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B0033, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M6700_6900.SplitData.node0032 := by
  change Tree.branch (150 : Fin 175) _ = Tree.branch (150 : Fin 175) _
  apply congrArg (Tree.branch (150 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0033
  · rfl
  · rfl

def B0031 : Block := .branch 125 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 181).pointIds 181), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B0032, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M6700_6900.SplitData.node0031 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0032
  · rfl

def B0030 : Block := .branch 164 ![288230376151712129, 72058693549557250, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0031]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M6700_6900.SplitData.node0030 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0031

def B0029 : Block := .branch 58 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0030, Tip0029_0102, (.leaf 2 (Common.fact 170).pointIds 170), (.leaf 3 (Common.fact 171).pointIds 171), (.leaf 4 (Common.fact 172).pointIds 172), (.leaf 5 (Common.fact 173).pointIds 173), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M6700_6900.SplitData.node0029 := by
  change Tree.branch (58 : Fin 175) _ = Tree.branch (58 : Fin 175) _
  apply congrArg (Tree.branch (58 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0030
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0029 : B0029.accepted = true := by decide +kernel
theorem checked0029 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0029 (maskNeeds ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0029]
  exact B0029.sound accepted0029
#print axioms checked0029

def Tip0028_0029 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0029 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0029
def B0379 : Block := .branch 112 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M6700_6900.SplitData.node0379 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0378 : Block := .branch 169 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 25815964921834847218632828946762079234078575359950912] ![B0379, (.leaf 1 (Common.fact 901).pointIds 901), (.leaf 2 (Common.fact 902).pointIds 902), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M6700_6900.SplitData.node0378 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0379
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0377 : Block := .branch 174 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 14965777479892292235385673216157722846024317431545872, 11150372599265311570767859136324180753383456, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 898).pointIds 898), (.leaf 1 (Common.fact 899).pointIds 899), (.leaf 2 (Common.fact 900).pointIds 900), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0378]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M6700_6900.SplitData.node0377 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0378

def B0376 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 895).pointIds 895), (.leaf 1 (Common.fact 896).pointIds 896), (.leaf 2 (Common.fact 897).pointIds 897), (.leaf 3 (Common.fact 798).pointIds 798), B0377, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M6700_6900.SplitData.node0376 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl
  · rfl

def B0375 : Block := .branch 59 ![42535295865118516858741440558145732993, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 894).pointIds 894), B0376, (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M6700_6900.SplitData.node0375 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0376
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0374 : Block := .branch 166 ![42535295865118516858741440558145732993, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1894106122002628253475232981739530557718248759492672] ![B0375, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M6700_6900.SplitData.node0374 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0375
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0373 : Block := .branch 164 ![42535295865118516858741440558145732993, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0374]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M6700_6900.SplitData.node0373 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0374

def B0372 : Block := .branch 125 ![1208925819614629174706561, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0373, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M6700_6900.SplitData.node0372 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0373
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0371 : Block := .branch 143 ![1208925819614629174706561, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0372, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M6700_6900.SplitData.node0371 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0372
  · rfl

def B0370 : Block := .branch 173 ![1208925819614629174706561, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 891).pointIds 891), (.leaf 1 (Common.fact 892).pointIds 892), (.leaf 2 (Common.fact 893).pointIds 893), (.leaf 3 (Common.fact 782).pointIds 782), B0371, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M6700_6900.SplitData.node0370 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0371
  · rfl
  · rfl

def B0369 : Block := .branch 170 ![1208925819614629174706561, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 888).pointIds 888), (.leaf 1 (Common.fact 889).pointIds 889), (.leaf 2 (Common.fact 890).pointIds 890), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0370]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M6700_6900.SplitData.node0369 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0370

def B0368 : Block := .branch 80 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0369, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M6700_6900.SplitData.node0368 := by
  change Tree.branch (80 : Fin 175) _ = Tree.branch (80 : Fin 175) _
  apply congrArg (Tree.branch (80 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0369
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0367 : Block := .branch 92 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0368, (.leaf 1 (Common.fact 441).pointIds 441), (.leaf 2 (Common.fact 442).pointIds 442), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 444).pointIds 444), (.leaf 5 (Common.fact 445).pointIds 445), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M6700_6900.SplitData.node0367 := by
  change Tree.branch (92 : Fin 175) _ = Tree.branch (92 : Fin 175) _
  apply congrArg (Tree.branch (92 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0366 : Block := .branch 168 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 435).pointIds 435), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 887).pointIds 887), (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), B0367]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M6700_6900.SplitData.node0366 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0367

def B0028 : Block := .branch 56 ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 165).pointIds 165), Tip0028_0029, B0366, (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), (.leaf 6 (Common.fact 169).pointIds 169)]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M6700_6900.SplitData.node0028 := by
  change Tree.branch (56 : Fin 175) _ = Tree.branch (56 : Fin 175) _
  apply congrArg (Tree.branch (56 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0366
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0028 : B0028.accepted = true := by decide +kernel
theorem checked0028 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0028 (maskNeeds ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0028]
  exact B0028.sound accepted0028
#print axioms checked0028

def B0393 : Block := .branch 112 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M6700_6900.SplitData.node0393 := by
  change Tree.branch (112 : Fin 175) _ = Tree.branch (112 : Fin 175) _
  apply congrArg (Tree.branch (112 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0392 : Block := .branch 169 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 25815964921834847218632828946762079234078575359950912] ![B0393, (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M6700_6900.SplitData.node0392 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0393
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0391 : Block := .branch 174 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 14965777479892292235385673216157722846024317431545872, 11150372599265311570767859136324180753383456, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 898).pointIds 898), (.leaf 1 (Common.fact 913).pointIds 913), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0392]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M6700_6900.SplitData.node0391 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0392

def B0390 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 895).pointIds 895), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 912).pointIds 912), (.leaf 3 (Common.fact 798).pointIds 798), B0391, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M6700_6900.SplitData.node0390 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0391
  · rfl
  · rfl

def B0389 : Block := .branch 59 ![42535295865118516858741440558145732993, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 894).pointIds 894), B0390, (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M6700_6900.SplitData.node0389 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0390
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0388 : Block := .branch 166 ![42535295865118516858741440558145732993, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1894106122002628253475232981739530557718248759492672] ![B0389, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M6700_6900.SplitData.node0388 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0389
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0387 : Block := .branch 164 ![42535295865118516858741440558145732993, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0388]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M6700_6900.SplitData.node0387 := by
  change Tree.branch (164 : Fin 175) _ = Tree.branch (164 : Fin 175) _
  apply congrArg (Tree.branch (164 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388

def B0386 : Block := .branch 125 ![1208925819614629174706561, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0387, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M6700_6900.SplitData.node0386 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0387
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0385 : Block := .branch 143 ![1208925819614629174706561, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0386, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M6700_6900.SplitData.node0385 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl

def B0384 : Block := .branch 173 ![1208925819614629174706561, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 891).pointIds 891), (.leaf 1 (Common.fact 909).pointIds 909), (.leaf 2 (Common.fact 910).pointIds 910), (.leaf 3 (Common.fact 782).pointIds 782), B0385, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M6700_6900.SplitData.node0384 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0385
  · rfl
  · rfl

def B0383 : Block := .branch 170 ![1208925819614629174706561, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 888).pointIds 888), (.leaf 1 (Common.fact 907).pointIds 907), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0384]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M6700_6900.SplitData.node0383 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0384

def B0382 : Block := .branch 80 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0383, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M6700_6900.SplitData.node0382 := by
  change Tree.branch (80 : Fin 175) _ = Tree.branch (80 : Fin 175) _
  apply congrArg (Tree.branch (80 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0383
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0381 : Block := .branch 92 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0382, (.leaf 1 (Common.fact 441).pointIds 441), (.leaf 2 (Common.fact 442).pointIds 442), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 444).pointIds 444), (.leaf 5 (Common.fact 445).pointIds 445), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M6700_6900.SplitData.node0381 := by
  change Tree.branch (92 : Fin 175) _ = Tree.branch (92 : Fin 175) _
  apply congrArg (Tree.branch (92 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0382
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0380 : Block := .branch 168 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 435).pointIds 435), (.leaf 1 (Common.fact 905).pointIds 905), (.leaf 2 (Common.fact 906).pointIds 906), (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), B0381]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M6700_6900.SplitData.node0380 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0381

theorem accepted0380 : B0380.accepted = true := by decide +kernel
theorem checked0380 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0380 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0380]
  exact B0380.sound accepted0380
#print axioms checked0380

end HexagonCover.NBand.M6700_6900.SplitTree.Run0004
