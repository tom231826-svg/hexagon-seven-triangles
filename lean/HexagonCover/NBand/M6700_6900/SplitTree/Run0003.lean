import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.NBand.M6700_6900.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip0117_0119 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0119 ![1208926972536133781553537, 72058693549557250, 77919046967349146032132, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6700_6900.SplitTree.Run0002.checked0119
def B0300 : Block := .branch 171 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 23945243539653359764829112828366565718790366975590416, 393248, 1496577676648622659723830243088744708080146344050752] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 797).pointIds 797), (.leaf 3 (Common.fact 798).pointIds 798), (.leaf 4 (Common.fact 799).pointIds 799), (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 800).pointIds 800)]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M6700_6900.SplitData.node0300 := by
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

def B0299 : Block := .branch 174 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 2244866514962044953844116877439481614143983806054464] ![(.leaf 0 (Common.fact 791).pointIds 791), (.leaf 1 (Common.fact 792).pointIds 792), (.leaf 2 (Common.fact 793).pointIds 793), (.leaf 3 (Common.fact 769).pointIds 769), B0300, (.leaf 5 (Common.fact 794).pointIds 794), (.leaf 6 (Common.fact 795).pointIds 795)]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M6700_6900.SplitData.node0299 := by
  change Tree.branch (174 : Fin 175) _ = Tree.branch (174 : Fin 175) _
  apply congrArg (Tree.branch (174 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0300
  · rfl
  · rfl

def B0298 : Block := .branch 169 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 1496577676648622659723830243088744708080146344050752] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 790).pointIds 790), B0299]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M6700_6900.SplitData.node0298 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0299

def B0297 : Block := .branch 143 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 393248, 1496577676648622659723830243088744708080146344050752] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0298, (.leaf 6 (Common.fact 786).pointIds 786)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M6700_6900.SplitData.node0297 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl

def B0296 : Block := .branch 173 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723830243088744708080146344050752] ![(.leaf 0 (Common.fact 779).pointIds 779), (.leaf 1 (Common.fact 780).pointIds 780), (.leaf 2 (Common.fact 781).pointIds 781), (.leaf 3 (Common.fact 782).pointIds 782), B0297, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M6700_6900.SplitData.node0296 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0297
  · rfl
  · rfl

def B0295 : Block := .branch 170 ![2535301200457611724498013258113, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 654).pointIds 654), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0296]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M6700_6900.SplitData.node0295 := by
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
  · exact treeEq0296

def B0294 : Block := .branch 101 ![1152921504606847361, 147646011283225970178, 21287542661060822571012, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0295, (.leaf 1 (Common.fact 222).pointIds 222), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M6700_6900.SplitData.node0294 := by
  change Tree.branch (101 : Fin 175) _ = Tree.branch (101 : Fin 175) _
  apply congrArg (Tree.branch (101 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0295
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0118 : Block := .branch 76 ![1208926972536133781553537, 147646011283225970178, 21287542661060822571012, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 281).pointIds 281), (.leaf 1 (Common.fact 282).pointIds 282), Tip0117_0119, (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 284).pointIds 284), (.leaf 5 (Common.fact 285).pointIds 285), B0294]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M6700_6900.SplitData.node0118 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0294

def B0309 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 14965776766268445882405732687014738121276749240172560, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M6700_6900.SplitData.node0309 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0308 : Block := .branch 174 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 14965776766268445882405732687014738121276749240172560, 393248, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 792).pointIds 792), (.leaf 2 (Common.fact 815).pointIds 815), (.leaf 3 (Common.fact 816).pointIds 816), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0309]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M6700_6900.SplitData.node0308 := by
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
  · exact treeEq0309

def B0307 : Block := .branch 171 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 11972621413014756705924586149611790497021399392157712, 393248, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 748).pointIds 748), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 813).pointIds 813), B0308, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M6700_6900.SplitData.node0307 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0308
  · rfl
  · rfl

def B0306 : Block := .branch 166 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1894106122002628253475232672254520736373180034711616] ![B0307, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M6700_6900.SplitData.node0306 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0307
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0305 : Block := .branch 164 ![42535295865118516859894362062752579969, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0306]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M6700_6900.SplitData.node0305 := by
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
  · exact treeEq0306

def B0304 : Block := .branch 125 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0305, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M6700_6900.SplitData.node0304 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0305
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0303 : Block := .branch 143 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0304, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M6700_6900.SplitData.node0303 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304
  · rfl

def B0302 : Block := .branch 173 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 803).pointIds 803), (.leaf 1 (Common.fact 780).pointIds 780), (.leaf 2 (Common.fact 804).pointIds 804), (.leaf 3 (Common.fact 805).pointIds 805), B0303, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M6700_6900.SplitData.node0302 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0303
  · rfl
  · rfl

def B0301 : Block := .branch 170 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 18889465931478580879368, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 801).pointIds 801), (.leaf 3 (Common.fact 802).pointIds 802), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0302]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M6700_6900.SplitData.node0301 := by
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
  · exact treeEq0302

def B0117 : Block := .branch 74 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 409).pointIds 409), (.leaf 1 (Common.fact 410).pointIds 410), B0118, B0301, (.leaf 4 (Common.fact 412).pointIds 412), (.leaf 5 (Common.fact 413).pointIds 413), (.leaf 6 (Common.fact 414).pointIds 414)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M6700_6900.SplitData.node0117 := by
  change Tree.branch (74 : Fin 175) _ = Tree.branch (74 : Fin 175) _
  apply congrArg (Tree.branch (74 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0118
  · exact treeEq0301
  · rfl
  · rfl
  · rfl

theorem accepted0117 : B0117.accepted = true := by decide +kernel
theorem checked0117 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0117 (maskNeeds ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0117]
  exact B0117.sound accepted0117
#print axioms checked0117

def Tip0115_0117 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0117 ![1208926972536133781553537, 147646011283225970178, 11842809695321532143620, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0117
def B0318 : Block := .branch 162 ![385, 1538, 6148, 38695070960633872881049608, 14965776766268445882405732687014738121276749240172560, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), (.leaf 3 (Common.fact 829).pointIds 829), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M6700_6900.SplitData.node0318 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0317 : Block := .branch 174 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 14965776766268445882405732687014738121276749240172560, 393248, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 792).pointIds 792), (.leaf 2 (Common.fact 827).pointIds 827), (.leaf 3 (Common.fact 828).pointIds 828), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0318]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M6700_6900.SplitData.node0317 := by
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
  · exact treeEq0318

def B0316 : Block := .branch 171 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 11972621413014756705924586149611790497021399392157712, 393248, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 748).pointIds 748), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 825).pointIds 825), (.leaf 3 (Common.fact 826).pointIds 826), B0317, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M6700_6900.SplitData.node0316 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0317
  · rfl
  · rfl

def B0315 : Block := .branch 166 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1894106122002628253475232672254520736373180034711616] ![B0316, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M6700_6900.SplitData.node0315 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0316
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0314 : Block := .branch 164 ![42535295865118516859894362062752579969, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0315]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M6700_6900.SplitData.node0314 := by
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
  · exact treeEq0315

def B0313 : Block := .branch 125 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0314, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M6700_6900.SplitData.node0313 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0314
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0312 : Block := .branch 143 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0313, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M6700_6900.SplitData.node0312 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0313
  · rfl

def B0311 : Block := .branch 173 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 803).pointIds 803), (.leaf 1 (Common.fact 780).pointIds 780), (.leaf 2 (Common.fact 823).pointIds 823), (.leaf 3 (Common.fact 824).pointIds 824), B0312, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M6700_6900.SplitData.node0311 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0312
  · rfl
  · rfl

def B0310 : Block := .branch 170 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 821).pointIds 821), (.leaf 3 (Common.fact 822).pointIds 822), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0311]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M6700_6900.SplitData.node0310 := by
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
  · exact treeEq0311

def B0116 : Block := .branch 73 ![1208926972536133781553537, 147646011283225970178, 7120443212451886929924, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), Tip0115_0117, B0310, (.leaf 4 (Common.fact 418).pointIds 418), (.leaf 5 (Common.fact 419).pointIds 419), (.leaf 6 (Common.fact 420).pointIds 420)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M6700_6900.SplitData.node0116 := by
  change Tree.branch (73 : Fin 175) _ = Tree.branch (73 : Fin 175) _
  apply congrArg (Tree.branch (73 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0310
  · rfl
  · rfl
  · rfl

def B0327 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 14965776766268445882405732687014738121276749240172560, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), (.leaf 3 (Common.fact 838).pointIds 838), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 360).pointIds 360), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M6700_6900.SplitData.node0327 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0326 : Block := .branch 174 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 14965776766268445882405732687014738121276749240172560, 393248, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 792).pointIds 792), (.leaf 2 (Common.fact 836).pointIds 836), (.leaf 3 (Common.fact 837).pointIds 837), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0327]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M6700_6900.SplitData.node0326 := by
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
  · exact treeEq0327

def B0325 : Block := .branch 171 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 11972621413014756705924586149611790497021399392157712, 393248, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 748).pointIds 748), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 834).pointIds 834), (.leaf 3 (Common.fact 835).pointIds 835), B0326, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M6700_6900.SplitData.node0325 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0326
  · rfl
  · rfl

def B0324 : Block := .branch 166 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1894106122002628253475232672254520736373180034711616] ![B0325, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M6700_6900.SplitData.node0324 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0325
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0323 : Block := .branch 164 ![42535295865118516859894362062752579969, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0324]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M6700_6900.SplitData.node0323 := by
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
  · exact treeEq0324

def B0322 : Block := .branch 125 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 11972621413014756705924586149611790497021399392157712, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0323, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M6700_6900.SplitData.node0322 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0323
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0321 : Block := .branch 143 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0322, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M6700_6900.SplitData.node0321 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0322
  · rfl

def B0320 : Block := .branch 173 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 803).pointIds 803), (.leaf 1 (Common.fact 780).pointIds 780), (.leaf 2 (Common.fact 832).pointIds 832), (.leaf 3 (Common.fact 833).pointIds 833), B0321, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M6700_6900.SplitData.node0320 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · rfl

def B0319 : Block := .branch 170 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 830).pointIds 830), (.leaf 3 (Common.fact 831).pointIds 831), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0320]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M6700_6900.SplitData.node0319 := by
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
  · exact treeEq0320

def B0115 : Block := .branch 72 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B0116, B0319, (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M6700_6900.SplitData.node0115 := by
  change Tree.branch (72 : Fin 175) _ = Tree.branch (72 : Fin 175) _
  apply congrArg (Tree.branch (72 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0116
  · exact treeEq0319
  · rfl
  · rfl
  · rfl

theorem accepted0115 : B0115.accepted = true := by decide +kernel
theorem checked0115 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0115 (maskNeeds ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0115]
  exact B0115.sound accepted0115
#print axioms checked0115

def Tip0113_0115 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0115 ![1208926972536133781553537, 147646011283225970178, 2398076729582241716228, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0115
def B0337 : Block := .branch 101 ![748288838313422294120286634350738058985342068851073, 1538, 6148, 24584, 98320, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 669).pointIds 669), (.leaf 1 (Common.fact 222).pointIds 222), (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M6700_6900.SplitData.node0337 := by
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

def B0336 : Block := .branch 169 ![1152921504606847361, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 25815964921834847218632828946762079234078575359950912] ![B0337, (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 847).pointIds 847), (.leaf 3 (Common.fact 848).pointIds 848), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M6700_6900.SplitData.node0336 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0337
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0335 : Block := .branch 174 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 14965777479892292235385673216157722846024317431545872, 11150372599265311570767859136324180753383456, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 792).pointIds 792), (.leaf 2 (Common.fact 845).pointIds 845), (.leaf 3 (Common.fact 846).pointIds 846), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0336]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M6700_6900.SplitData.node0335 := by
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
  · exact treeEq0336

def B0334 : Block := .branch 171 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 748).pointIds 748), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 843).pointIds 843), (.leaf 3 (Common.fact 844).pointIds 844), B0335, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M6700_6900.SplitData.node0334 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl
  · rfl

def B0333 : Block := .branch 166 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1894106122002628253475232672254520736373180034711616] ![B0334, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M6700_6900.SplitData.node0333 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0334
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0332 : Block := .branch 164 ![42535295865118516859894362062752579969, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0333]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M6700_6900.SplitData.node0332 := by
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
  · exact treeEq0333

def B0331 : Block := .branch 125 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0332, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M6700_6900.SplitData.node0331 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0332
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0330 : Block := .branch 143 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0331, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M6700_6900.SplitData.node0330 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0331
  · rfl

def B0329 : Block := .branch 173 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 803).pointIds 803), (.leaf 1 (Common.fact 780).pointIds 780), (.leaf 2 (Common.fact 841).pointIds 841), (.leaf 3 (Common.fact 842).pointIds 842), B0330, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M6700_6900.SplitData.node0329 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl
  · rfl

def B0328 : Block := .branch 170 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 744).pointIds 744), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 839).pointIds 839), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0329]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M6700_6900.SplitData.node0328 := by
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
  · exact treeEq0329

def B0114 : Block := .branch 71 ![1208926972536133781553537, 147646011283225970178, 36893488147419109380, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), Tip0113_0115, B0328, (.leaf 4 (Common.fact 298).pointIds 298), (.leaf 5 (Common.fact 299).pointIds 299), (.leaf 0 [] 0)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M6700_6900.SplitData.node0114 := by
  change Tree.branch (71 : Fin 175) _ = Tree.branch (71 : Fin 175) _
  apply congrArg (Tree.branch (71 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0328
  · rfl
  · rfl
  · rfl

def B0345 : Block := .branch 119 ![385, 1538, 6148, 79228162514264337593543974920, 5444517870735015415413993718908291481616, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 162).pointIds 162), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M6700_6900.SplitData.node0345 := by
  change Tree.branch (119 : Fin 175) _ = Tree.branch (119 : Fin 175) _
  apply congrArg (Tree.branch (119 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0344 : Block := .branch 132 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0345, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 857).pointIds 857)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M6700_6900.SplitData.node0344 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl
  · rfl

def B0343 : Block := .branch 135 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), B0344, (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M6700_6900.SplitData.node0343 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl

def B0342 : Block := .branch 138 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0343, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M6700_6900.SplitData.node0342 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0343
  · rfl
  · rfl

def B0341 : Block := .branch 139 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0342, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M6700_6900.SplitData.node0341 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl

def B0340 : Block := .branch 140 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0341, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 853).pointIds 853)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M6700_6900.SplitData.node0340 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0341
  · rfl
  · rfl

def B0339 : Block := .branch 141 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0340, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M6700_6900.SplitData.node0339 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0340
  · rfl
  · rfl

def B0338 : Block := .branch 144 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), B0339, (.leaf 6 (Common.fact 851).pointIds 851)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M6700_6900.SplitData.node0338 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0339
  · rfl

def B0113 : Block := .branch 67 ![1208926972536133781553537, 72058693549557250, 36893488147419109380, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 462).pointIds 462), B0114, (.leaf 2 (Common.fact 463).pointIds 463), (.leaf 3 (Common.fact 464).pointIds 464), (.leaf 4 (Common.fact 465).pointIds 465), (.leaf 5 (Common.fact 466).pointIds 466), B0338]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M6700_6900.SplitData.node0113 := by
  change Tree.branch (67 : Fin 175) _ = Tree.branch (67 : Fin 175) _
  apply congrArg (Tree.branch (67 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0114
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0338

theorem accepted0113 : B0113.accepted = true := by decide +kernel
theorem checked0113 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0113 (maskNeeds ![1208926972536133781553537, 72058693549557250, 36893488147419109380, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0113]
  exact B0113.sound accepted0113
#print axioms checked0113

def Tip0112_0113 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0113 ![1208926972536133781553537, 72058693549557250, 36893488147419109380, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked0113
def B0356 : Block := .branch 170 ![21267649200209254195843235965795565953, 730750818665451459101842416358141510927477900802, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 23384026219072518174515931635210454029199436415040] ![(.leaf 0 (Common.fact 620).pointIds 620), (.leaf 1 (Common.fact 549).pointIds 549), (.leaf 2 (Common.fact 869).pointIds 869), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 767).pointIds 767), (.leaf 6 (Common.fact 870).pointIds 870)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M6700_6900.SplitData.node0356 := by
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
  · rfl

def B0355 : Block := .branch 100 ![21267647932558653967613834469092360577, 730750818665451459101842416358141510927477900802, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 23384026219072518174515931635210454029199436415040] ![B0356, (.leaf 1 (Common.fact 509).pointIds 509), (.leaf 2 (Common.fact 510).pointIds 510), (.leaf 3 (Common.fact 511).pointIds 511), (.leaf 4 (Common.fact 512).pointIds 512), (.leaf 5 (Common.fact 513).pointIds 513), (.leaf 6 (Common.fact 868).pointIds 868)]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M6700_6900.SplitData.node0355 := by
  change Tree.branch (100 : Fin 175) _ = Tree.branch (100 : Fin 175) _
  apply congrArg (Tree.branch (100 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0356
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0354 : Block := .branch 159 ![21267647932558653967613834469092360577, 1099511629314, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 23384026219072518174515931635210454029199436415040] ![(.leaf 0 (Common.fact 866).pointIds 866), B0355, (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), (.leaf 6 (Common.fact 867).pointIds 867)]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M6700_6900.SplitData.node0354 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0353 : Block := .branch 164 ![21267647932558653967613834469092360577, 1099511629314, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0354]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M6700_6900.SplitData.node0353 := by
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
  · exact treeEq0354

def B0352 : Block := .branch 124 ![1152921504606847361, 1099511629314, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 43556142965880123323311949751266331459616, 21778071483256974311749925714704515727424] ![B0353, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 204).pointIds 204), (.leaf 6 (Common.fact 865).pointIds 865)]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M6700_6900.SplitData.node0352 := by
  change Tree.branch (124 : Fin 175) _ = Tree.branch (124 : Fin 175) _
  apply congrArg (Tree.branch (124 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0353
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0351 : Block := .branch 135 ![1152921504606847361, 1099511629314, 18482772870728521732, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), B0352, (.leaf 6 (Common.fact 864).pointIds 864)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M6700_6900.SplitData.node0351 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl

def B0350 : Block := .branch 138 ![1152921504606847361, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 3484491437270409865864955980101306485407760, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0351, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 863).pointIds 863)]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M6700_6900.SplitData.node0350 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0351
  · rfl
  · rfl

def B0349 : Block := .branch 139 ![1152921504606847361, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0350, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M6700_6900.SplitData.node0349 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0350
  · rfl
  · rfl

def B0348 : Block := .branch 140 ![1152921504606847361, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0349, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 861).pointIds 861)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M6700_6900.SplitData.node0348 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0349
  · rfl
  · rfl

def B0347 : Block := .branch 141 ![1152921504606847361, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0348, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M6700_6900.SplitData.node0347 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0348
  · rfl
  · rfl

def B0346 : Block := .branch 144 ![1152921504606847361, 1099511629314, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), B0347, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M6700_6900.SplitData.node0346 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0347
  · rfl

def B0112 : Block := .branch 65 ![1208926972536133781553537, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), Tip0112_0113, (.leaf 3 (Common.fact 136).pointIds 136), (.leaf 4 (Common.fact 137).pointIds 137), (.leaf 5 (Common.fact 138).pointIds 138), B0346]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M6700_6900.SplitData.node0112 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0346

theorem accepted0112 : B0112.accepted = true := by decide +kernel
theorem checked0112 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0112 (maskNeeds ![1208926972536133781553537, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq0112]
  exact B0112.sound accepted0112
#print axioms checked0112

end HexagonCover.NBand.M6700_6900.SplitTree.Run0003
