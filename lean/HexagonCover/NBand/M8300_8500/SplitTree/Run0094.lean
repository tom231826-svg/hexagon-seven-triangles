import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0093
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0094
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6730_6812 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6812 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89202980794771529673459726544159758065172496, 233840261972944466912589573234605283144949207269408, 2993155364425908967085178985457853733422848099745856] HexagonCover.NBand.M8300_8500.SplitTree.Run0093.checked6812
def Tip6730_6733 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6733 ![57116533094483332143236956324626817, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 649037107316853453566312041250832, 42535295865117307932921825928971419680, 2993155364425866431789313868149920811596919128719424] HexagonCover.NBand.M8300_8500.SplitTree.Run0093.checked6733
def B6811 : Block := .branch 165 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89202983453227521243291472351773878625861648, 187072209578355573530071658587684226515959365894176, 2993155364425908967085178985457853733422848099745856] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 569).pointIds 569), Tip6730_6812, (.leaf 0 [] 0)]
theorem treeEq6811 : B6811.tree = HexagonCover.NBand.M8300_8500.SplitData.node6811 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6810 : Block := .branch 167 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 89202983453227521243291472351773878625861648, 393248, 2993155364425908967085178985457853733422848099745856] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 568).pointIds 568), B6811, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6810 : B6810.tree = HexagonCover.NBand.M8300_8500.SplitData.node6810 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6811
  · rfl

def B6809 : Block := .branch 146 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 1496577676626845252854650389321924528368798608154632, 2659105028677148599261180432601939984, 393248, 2993155364425908967085178985457853733422848099745856] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 567).pointIds 567), B6810, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6809 : B6809.tree = HexagonCover.NBand.M8300_8500.SplitData.node6809 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6810
  · rfl
  · rfl

def B6808 : Block := .branch 170 ![46731939377413676886175963666186625, 146437906389534210, 4840444091685460053596164, 664614077120620450716241123684147208, 2659105028677148599261180432601939984, 393248, 2993155364425908967085178985457853733422848099745856] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6809, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1153).pointIds 1153)]
theorem treeEq6808 : B6808.tree = HexagonCover.NBand.M8300_8500.SplitData.node6808 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6809
  · rfl
  · rfl
  · rfl

def B6732 : Block := .branch 125 ![57116533095087795053044270911979905, 146437906389534210, 14511850648602493451245572, 664614235576945479244916310772047880, 2659105028677148599261180432601939984, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), Tip6730_6733, B6808]
theorem treeEq6732 : B6732.tree = HexagonCover.NBand.M8300_8500.SplitData.node6732 := by
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
  · exact treeEq6808

def B6835 : Block := .branch 174 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 14965776777418821140127035827614343065215600309043264] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1193).pointIds 1193), (.leaf 3 (Common.fact 1194).pointIds 1194), (.leaf 4 (Common.fact 1195).pointIds 1195), (.leaf 5 (Common.fact 1196).pointIds 1196), (.leaf 6 (Common.fact 1197).pointIds 1197)]
theorem treeEq6835 : B6835.tree = HexagonCover.NBand.M8300_8500.SplitData.node6835 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6834 : Block := .branch 173 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 2993155364404064434202449678002552568194200916983872] ![(.leaf 0 (Common.fact 1186).pointIds 1186), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1141).pointIds 1141), (.leaf 4 (Common.fact 1189).pointIds 1189), (.leaf 5 (Common.fact 1190).pointIds 1190), B6835]
theorem treeEq6834 : B6834.tree = HexagonCover.NBand.M8300_8500.SplitData.node6834 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6835

def B6833 : Block := .branch 144 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 5708990770823839524233143877797980545531379744, 2993155364425863773333322298318175003982798568030272] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B6834, (.leaf 6 (Common.fact 1185).pointIds 1185)]
theorem treeEq6833 : B6833.tree = HexagonCover.NBand.M8300_8500.SplitData.node6833 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6834
  · rfl

def B6832 : Block := .branch 152 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 664614156348782964980578717228097544, 649037107316853453566312041250832, 393248, 2993155364425863773333322298318175003982798568030272] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B6833, (.leaf 6 (Common.fact 1184).pointIds 1184)]
theorem treeEq6832 : B6832.tree = HexagonCover.NBand.M8300_8500.SplitData.node6832 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6833
  · rfl

def B6731 : Block := .branch 121 ![57116533095087795053044270911979905, 377789465067478006629890, 53235255808133584203552772, 664614235576945479244916310772047880, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B6732, (.leaf 5 (Common.fact 256).pointIds 256), B6832]
theorem treeEq6731 : B6731.tree = HexagonCover.NBand.M8300_8500.SplitData.node6731 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6732
  · rfl
  · exact treeEq6832

def B6842 : Block := .branch 174 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 14977468790517465705016673736444327521758727208697920] ![(.leaf 0 (Common.fact 1191).pointIds 1191), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1193).pointIds 1193), (.leaf 3 (Common.fact 1203).pointIds 1203), (.leaf 4 (Common.fact 1204).pointIds 1204), (.leaf 5 (Common.fact 1205).pointIds 1205), (.leaf 6 (Common.fact 1206).pointIds 1206)]
theorem treeEq6842 : B6842.tree = HexagonCover.NBand.M8300_8500.SplitData.node6842 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6841 : Block := .branch 173 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233845993264460489282736947914201353773856244236320, 3004847377502708999092087586832537024737327816638528] ![(.leaf 0 (Common.fact 1186).pointIds 1186), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1201).pointIds 1201), (.leaf 5 (Common.fact 1202).pointIds 1202), B6842]
theorem treeEq6841 : B6841.tree = HexagonCover.NBand.M8300_8500.SplitData.node6841 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6842

def B6840 : Block := .branch 144 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233845970963715290752113806378483081125494738255904, 3004847377524508338222960207148159460525925467684928] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B6841, (.leaf 6 (Common.fact 1199).pointIds 1199)]
theorem treeEq6840 : B6840.tree = HexagonCover.NBand.M8300_8500.SplitData.node6840 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6841
  · rfl

def B6839 : Block := .branch 152 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 3004847377524508338222960207148159460525925467684928] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B6840, (.leaf 6 (Common.fact 1198).pointIds 1198)]
theorem treeEq6839 : B6839.tree = HexagonCover.NBand.M8300_8500.SplitData.node6839 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6840
  · rfl

def B6838 : Block := .branch 163 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 233840261972944466912589573234605283144949207269408, 2993155364425861114877330728486429196368678007341120] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B6839]
theorem treeEq6838 : B6838.tree = HexagonCover.NBand.M8300_8500.SplitData.node6838 := by
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
  · exact treeEq6839

def B6837 : Block := .branch 165 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 187072209578355573530071658587684226515959365894176, 2993155364425861114877330728486429196368678007341120] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B6838, (.leaf 0 [] 0)]
theorem treeEq6837 : B6837.tree = HexagonCover.NBand.M8300_8500.SplitData.node6837 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6838
  · rfl

def B6836 : Block := .branch 167 ![57116533094483332143236956324626817, 377789320881921186596354, 53230514994906640848787460, 158456325028528675187087925256, 665263034999774789905469842181423120, 393248, 2993155364425861114877330728486429196368678007341120] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B6837, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6836 : B6836.tree = HexagonCover.NBand.M8300_8500.SplitData.node6836 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6837
  · rfl

def B6730 : Block := .branch 119 ![57116533095087795053044270911979905, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B6731, B6836, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1075).pointIds 1075)]
theorem treeEq6730 : B6730.tree = HexagonCover.NBand.M8300_8500.SplitData.node6730 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6731
  · exact treeEq6836
  · rfl
  · rfl

theorem accepted6730 : B6730.accepted = true := by decide +kernel
theorem checked6730 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6730 (maskNeeds ![57116533095087795053044270911979905, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6730]
  exact B6730.sound accepted6730
#print axioms checked6730

def Tip6729_6730 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6730 ![57116533095087795053044270911979905, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] checked6730
def B6856 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 795422266117343954770730338484458061691711920668704, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 1222).pointIds 1222), (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq6856 : B6856.tree = HexagonCover.NBand.M8300_8500.SplitData.node6856 := by
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
  · rfl

def B6855 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 47133427803921660650443704133721155627874458664992, 38911022446793344706174667102810258014310370544975936] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6856, (.leaf 6 (Common.fact 1221).pointIds 1221)]
theorem treeEq6855 : B6855.tree = HexagonCover.NBand.M8300_8500.SplitData.node6855 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6856
  · rfl

def B6854 : Block := .branch 151 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 11692102650077161844200138707952406327136174047248, 47133427803921660650443704133721155627874458664992, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), B6855]
theorem treeEq6854 : B6854.tree = HexagonCover.NBand.M8300_8500.SplitData.node6854 := by
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
  · exact treeEq6855

def B6853 : Block := .branch 158 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 11692102650077161844200138707952406327136174047248, 46768052394588934920892782925542084872960475529248, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), (.leaf 4 (Common.fact 1220).pointIds 1220), B6854, (.leaf 0 [] 0)]
theorem treeEq6853 : B6853.tree = HexagonCover.NBand.M8300_8500.SplitData.node6853 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6854
  · rfl

def B6852 : Block := .branch 163 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 89551429938498570660046222142169888713703440, 46768052394588934920892782925542084872960475529248, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6853, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq6852 : B6852.tree = HexagonCover.NBand.M8300_8500.SplitData.node6852 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6853
  · rfl
  · rfl

def B6851 : Block := .branch 174 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 89551429938498570660046222142169888713703440, 46768052394588934920892782925542084872960475529248, 14965776766268445882405732687014738121277298995363904] ![(.leaf 0 (Common.fact 1217).pointIds 1217), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1193).pointIds 1193), (.leaf 3 (Common.fact 1203).pointIds 1203), (.leaf 4 (Common.fact 1195).pointIds 1195), (.leaf 5 (Common.fact 1218).pointIds 1218), B6852]
theorem treeEq6851 : B6851.tree = HexagonCover.NBand.M8300_8500.SplitData.node6851 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6852

def B6850 : Block := .branch 86 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89551429938498570660046222142169888713703440, 46768052394588934920892782925542084872960475529248, 14965776777418818481671044257782597257601479748354112] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6851, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1216).pointIds 1216)]
theorem treeEq6850 : B6850.tree = HexagonCover.NBand.M8300_8500.SplitData.node6850 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6851
  · rfl
  · rfl
  · rfl
  · rfl

def B6849 : Block := .branch 138 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 46768052394588934920892782925542084872960475529248, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6850, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6849 : B6849.tree = HexagonCover.NBand.M8300_8500.SplitData.node6849 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6850
  · rfl
  · rfl

def B6848 : Block := .branch 165 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 41538374868278621028243970634154016, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6849, (.leaf 0 [] 0)]
theorem treeEq6848 : B6848.tree = HexagonCover.NBand.M8300_8500.SplitData.node6848 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6849
  · rfl

def B6847 : Block := .branch 167 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 41538374868278621028243970634154016, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6848, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6847 : B6847.tree = HexagonCover.NBand.M8300_8500.SplitData.node6847 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6848
  · rfl

def B6846 : Block := .branch 146 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 649037107316853453566312041250832, 41538374868278621028243970634154016, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6847, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6846 : B6846.tree = HexagonCover.NBand.M8300_8500.SplitData.node6846 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6847
  · rfl
  · rfl

def B6845 : Block := .branch 170 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 41538374868278621028243970634154016, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6846, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1215).pointIds 1215)]
theorem treeEq6845 : B6845.tree = HexagonCover.NBand.M8300_8500.SplitData.node6845 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6846
  · rfl
  · rfl
  · rfl

def B6844 : Block := .branch 172 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 41538374868278621028243970634154016, 14965776777440623137713900017761711308618318520778816] ![B6845, (.leaf 1 (Common.fact 1209).pointIds 1209), (.leaf 2 (Common.fact 1210).pointIds 1210), (.leaf 3 (Common.fact 1211).pointIds 1211), (.leaf 4 (Common.fact 1212).pointIds 1212), (.leaf 5 (Common.fact 1213).pointIds 1213), (.leaf 6 (Common.fact 1214).pointIds 1214)]
theorem treeEq6844 : B6844.tree = HexagonCover.NBand.M8300_8500.SplitData.node6844 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6845
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6843 : Block := .branch 173 ![15578158226204711114992985690866049, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 41538374868278621028243970634154016, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1207).pointIds 1207), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1189).pointIds 1189), (.leaf 5 (Common.fact 1208).pointIds 1208), B6844]
theorem treeEq6843 : B6843.tree = HexagonCover.NBand.M8300_8500.SplitData.node6843 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6844

def B6729 : Block := .branch 115 ![15578158226809174024800300278219137, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![Tip6729_6730, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B6843, (.leaf 0 [] 0)]
theorem treeEq6729 : B6729.tree = HexagonCover.NBand.M8300_8500.SplitData.node6729 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6843
  · rfl

theorem accepted6729 : B6729.accepted = true := by decide +kernel
theorem checked6729 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6729 (maskNeeds ![15578158226809174024800300278219137, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6729]
  exact B6729.sound accepted6729
#print axioms checked6729

def B6882 : Block := .branch 135 ![385, 1538, 6148, 24584, 98320, 795422266117343913232355470205837033447741286907936, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 1242).pointIds 1242), (.leaf 6 (Common.fact 1223).pointIds 1223)]
theorem treeEq6882 : B6882.tree = HexagonCover.NBand.M8300_8500.SplitData.node6882 := by
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
  · rfl

def B6881 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 649037107316853453566312041250832, 47133427803921619112068835855100127383903824904224, 38911022446793344706174667102810258014310370544975936] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), B6882, (.leaf 6 (Common.fact 1221).pointIds 1221)]
theorem treeEq6881 : B6881.tree = HexagonCover.NBand.M8300_8500.SplitData.node6881 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6882
  · rfl

def B6880 : Block := .branch 151 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 11692102650077161844200138707952406327136174047248, 47133427803921619112068835855100127383903824904224, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 597).pointIds 597), (.leaf 5 (Common.fact 300).pointIds 300), B6881]
theorem treeEq6880 : B6880.tree = HexagonCover.NBand.M8300_8500.SplitData.node6880 := by
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
  · exact treeEq6881

def B6879 : Block := .branch 158 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 11692102650077161844200138707952406327136174047248, 46768052394588893382517914646921056628989841768480, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 306).pointIds 306), (.leaf 1 (Common.fact 307).pointIds 307), (.leaf 2 (Common.fact 308).pointIds 308), (.leaf 3 (Common.fact 309).pointIds 309), (.leaf 4 (Common.fact 1220).pointIds 1220), B6880, (.leaf 0 [] 0)]
theorem treeEq6879 : B6879.tree = HexagonCover.NBand.M8300_8500.SplitData.node6879 := by
  change Tree.branch (158 : Fin 177) _ = Tree.branch (158 : Fin 177) _
  apply congrArg (Tree.branch (158 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6880
  · rfl

def B6878 : Block := .branch 163 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 89551429938498570660046222142169888713703440, 46768052394588893382517914646921056628989841768480, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6879, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq6878 : B6878.tree = HexagonCover.NBand.M8300_8500.SplitData.node6878 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6879
  · rfl
  · rfl

def B6877 : Block := .branch 174 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 89551429938498570660046222142169888713703440, 46768052394588893382517914646921056628989841768480, 14965776766268445882405732687014738121277298995363904] ![(.leaf 0 (Common.fact 1240).pointIds 1240), (.leaf 1 (Common.fact 1192).pointIds 1192), (.leaf 2 (Common.fact 1193).pointIds 1193), (.leaf 3 (Common.fact 1203).pointIds 1203), (.leaf 4 (Common.fact 1195).pointIds 1195), (.leaf 5 (Common.fact 1241).pointIds 1241), B6878]
theorem treeEq6877 : B6877.tree = HexagonCover.NBand.M8300_8500.SplitData.node6877 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6878

def B6876 : Block := .branch 86 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89551429938498570660046222142169888713703440, 46768052394588893382517914646921056628989841768480, 14965776777418818481671044257782597257601479748354112] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6877, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1216).pointIds 1216)]
theorem treeEq6876 : B6876.tree = HexagonCover.NBand.M8300_8500.SplitData.node6876 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6877
  · rfl
  · rfl
  · rfl
  · rfl

def B6875 : Block := .branch 138 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 46768052394588893382517914646921056628989841768480, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6876, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6875 : B6875.tree = HexagonCover.NBand.M8300_8500.SplitData.node6875 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6876
  · rfl
  · rfl

def B6874 : Block := .branch 165 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 393248, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6875, (.leaf 0 [] 0)]
theorem treeEq6874 : B6874.tree = HexagonCover.NBand.M8300_8500.SplitData.node6874 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6875
  · rfl

def B6873 : Block := .branch 167 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 89202980794771529673459726544159758065172496, 393248, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6874, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6873 : B6873.tree = HexagonCover.NBand.M8300_8500.SplitData.node6873 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6874
  · rfl

def B6872 : Block := .branch 146 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 1496577676626844588240810953189016605140455555883016, 649037107316853453566312041250832, 393248, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6873, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6872 : B6872.tree = HexagonCover.NBand.M8300_8500.SplitData.node6872 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6873
  · rfl
  · rfl

def B6871 : Block := .branch 170 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 14965776777440623137713900017761711308618318520778816] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6872, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1215).pointIds 1215)]
theorem treeEq6871 : B6871.tree = HexagonCover.NBand.M8300_8500.SplitData.node6871 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6872
  · rfl
  · rfl
  · rfl

def B6870 : Block := .branch 172 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 14965776777440623137713900017761711308618318520778816] ![B6871, (.leaf 1 (Common.fact 1209).pointIds 1209), (.leaf 2 (Common.fact 1210).pointIds 1210), (.leaf 3 (Common.fact 1211).pointIds 1211), (.leaf 4 (Common.fact 1212).pointIds 1212), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1214).pointIds 1214)]
theorem treeEq6870 : B6870.tree = HexagonCover.NBand.M8300_8500.SplitData.node6870 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6871
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6869 : Block := .branch 173 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 1237).pointIds 1237), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1189).pointIds 1189), (.leaf 5 (Common.fact 1238).pointIds 1238), B6870]
theorem treeEq6869 : B6869.tree = HexagonCover.NBand.M8300_8500.SplitData.node6869 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6870

theorem accepted6869 : B6869.accepted = true := by decide +kernel
theorem checked6869 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6869 (maskNeeds ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6869]
  exact B6869.sound accepted6869
#print axioms checked6869

def Tip6727_6729 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6729 ![15578158226809174024800300278219137, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] checked6729
def Tip6727_6869 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6869 ![1267650600228229401496703205761, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] checked6869
def B6868 : Block := .branch 163 ![385, 1538, 6148, 24584, 2943698366206691291790031665443150030830665744, 393248, 15714065604581868186910613038435130284402129115807808] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1086).pointIds 1086), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1236).pointIds 1236)]
theorem treeEq6868 : B6868.tree = HexagonCover.NBand.M8300_8500.SplitData.node6868 := by
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

def B6867 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 2854495385412568799223888792352556584806744080, 393248, 15714065604581868186910613038435130284402129115807808] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6868, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6867 : B6867.tree = HexagonCover.NBand.M8300_8500.SplitData.node6867 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6868
  · rfl
  · rfl

def B6866 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 2854495385412568799223888792352556584806744080, 393248, 15714065604581868186910613038435130284402129115807808] ![(.leaf 0 (Common.fact 577).pointIds 577), B6867, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 1235).pointIds 1235)]
theorem treeEq6866 : B6866.tree = HexagonCover.NBand.M8300_8500.SplitData.node6866 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6867
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6865 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 2854495385412568799223888792352556584806744080, 393248, 15714065604581868186910613038435130284402129115807808] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B6866, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 1234).pointIds 1234)]
theorem treeEq6865 : B6865.tree = HexagonCover.NBand.M8300_8500.SplitData.node6865 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6866
  · rfl
  · rfl
  · rfl
  · rfl

def B6864 : Block := .branch 170 ![385, 146437906389534210, 4840444091685460053596164, 24584, 2854495385412568799223888792352556584806744080, 393248, 15714065604581868186910613038435130284402129115807808] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6865, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1233).pointIds 1233)]
theorem treeEq6864 : B6864.tree = HexagonCover.NBand.M8300_8500.SplitData.node6864 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6865
  · rfl
  · rfl
  · rfl

def B6863 : Block := .branch 173 ![5193564509135055857931993032425857, 377789465067478006629890, 53235255808133584203552772, 158456325028528675187087925256, 2854495385412568799223888792352556584806744080, 5709034369502101269473775122669557740833472544, 3741444191567111480986026888823339787380729723748416] ![(.leaf 0 (Common.fact 1231).pointIds 1231), (.leaf 1 (Common.fact 1187).pointIds 1187), (.leaf 2 (Common.fact 1188).pointIds 1188), (.leaf 3 (Common.fact 1200).pointIds 1200), (.leaf 4 (Common.fact 1118).pointIds 1118), (.leaf 5 (Common.fact 1232).pointIds 1232), B6864]
theorem treeEq6863 : B6863.tree = HexagonCover.NBand.M8300_8500.SplitData.node6863 := by
  change Tree.branch (173 : Fin 177) _ = Tree.branch (173 : Fin 177) _
  apply congrArg (Tree.branch (173 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6864

def B6862 : Block := .branch 172 ![5193564509135055857931993032425857, 377789465067478006629890, 53235255808133584203552772, 158456325028528675187087925256, 2854495385412568799223888792352556584806744080, 5709034369502101269473775122669557740833472544, 3741444191567111480986026888823339787380729723748416] ![B6863, (.leaf 1 (Common.fact 1209).pointIds 1209), (.leaf 2 (Common.fact 1210).pointIds 1210), (.leaf 3 (Common.fact 1211).pointIds 1211), (.leaf 4 (Common.fact 1228).pointIds 1228), (.leaf 5 (Common.fact 1229).pointIds 1229), (.leaf 6 (Common.fact 1230).pointIds 1230)]
theorem treeEq6862 : B6862.tree = HexagonCover.NBand.M8300_8500.SplitData.node6862 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6863
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6861 : Block := .branch 125 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 158456325028528675187087925256, 2854495385412568799223888792352556584806744080, 5709034326966805404356467189747731811862446112, 3741444191567111480986026888823339787380729723748416] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B6862, (.leaf 6 (Common.fact 1227).pointIds 1227)]
theorem treeEq6861 : B6861.tree = HexagonCover.NBand.M8300_8500.SplitData.node6861 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6862
  · rfl

def B6860 : Block := .branch 151 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 158456325028528675187087925256, 649037107316853453566312041250832, 5709034326966805404356467189747731811862446112, 3741444191567111480986026888823339787380729723748416] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6861, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1226).pointIds 1226)]
theorem treeEq6860 : B6860.tree = HexagonCover.NBand.M8300_8500.SplitData.node6860 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6861
  · rfl
  · rfl

def B6859 : Block := .branch 152 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 158456325028528675187087925256, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 3741444191567111480986026888823339787380729723748416] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B6860, (.leaf 6 (Common.fact 1225).pointIds 1225)]
theorem treeEq6859 : B6859.tree = HexagonCover.NBand.M8300_8500.SplitData.node6859 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6860
  · rfl

def B6858 : Block := .branch 169 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 43556142965880123323311949751266331459616, 2993155353253689186865740254472602881316892261744704] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 589).pointIds 589), B6859]
theorem treeEq6858 : B6858.tree = HexagonCover.NBand.M8300_8500.SplitData.node6858 := by
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
  · exact treeEq6859

def B6857 : Block := .branch 135 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425839857613991886902117992516706180268096] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B6858, (.leaf 6 (Common.fact 1224).pointIds 1224)]
theorem treeEq6857 : B6857.tree = HexagonCover.NBand.M8300_8500.SplitData.node6857 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6858
  · rfl

def B6728 : Block := .branch 113 ![5193564509739518767739307619778945, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![Tip6727_6729, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B6857]
theorem treeEq6728 : B6728.tree = HexagonCover.NBand.M8300_8500.SplitData.node6728 := by
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
  · exact treeEq6857

def B6727 : Block := .branch 112 ![1267651204691139208811290558849, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![B6728, (.leaf 1 (Common.fact 233).pointIds 233), (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), Tip6727_6869]
theorem treeEq6727 : B6727.tree = HexagonCover.NBand.M8300_8500.SplitData.node6727 := by
  change Tree.branch (112 : Fin 177) _ = Tree.branch (112 : Fin 177) _
  apply congrArg (Tree.branch (112 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6728
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6727 : B6727.accepted = true := by decide +kernel
theorem checked6727 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6727 (maskNeeds ![1267651204691139208811290558849, 377789465067478006629890, 53235255808133584203552772, 237684487542793012780631875592, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6727]
  exact B6727.sound accepted6727
#print axioms checked6727

def B6898 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 1252).pointIds 1252)]
theorem treeEq6898 : B6898.tree = HexagonCover.NBand.M8300_8500.SplitData.node6898 := by
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

def B6897 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6898, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1146).pointIds 1146)]
theorem treeEq6897 : B6897.tree = HexagonCover.NBand.M8300_8500.SplitData.node6897 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6898
  · rfl
  · rfl

def B6896 : Block := .branch 89 ![374144419156711147061410967775596682433415434207617, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 1250).pointIds 1250), B6897, (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), (.leaf 6 (Common.fact 1251).pointIds 1251)]
theorem treeEq6896 : B6896.tree = HexagonCover.NBand.M8300_8500.SplitData.node6896 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6897
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6895 : Block := .branch 168 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 89551429937849533552729368688603576672550928, 393248, 749750339950774464686422877837419649997007635349568] ![B6896, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1249).pointIds 1249)]
theorem treeEq6895 : B6895.tree = HexagonCover.NBand.M8300_8500.SplitData.node6895 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6896
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6894 : Block := .branch 87 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89551429937849533552729368688603576672550928, 393248, 749750339950774464686422877837419649997007635349568] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B6895, (.leaf 3 (Common.fact 1247).pointIds 1247), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 1248).pointIds 1248)]
theorem treeEq6894 : B6894.tree = HexagonCover.NBand.M8300_8500.SplitData.node6894 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6895
  · rfl
  · rfl
  · rfl
  · rfl

def B6893 : Block := .branch 138 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89202980794122492566142873090593446024019984, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B6894, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6893 : B6893.tree = HexagonCover.NBand.M8300_8500.SplitData.node6893 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6894
  · rfl
  · rfl

def B6892 : Block := .branch 165 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89202980794771529673459726544159758065172496, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B6893, (.leaf 0 [] 0)]
theorem treeEq6892 : B6892.tree = HexagonCover.NBand.M8300_8500.SplitData.node6892 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6893
  · rfl

def B6891 : Block := .branch 167 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 89202980794771529673459726544159758065172496, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B6892, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6891 : B6891.tree = HexagonCover.NBand.M8300_8500.SplitData.node6891 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6892
  · rfl

def B6890 : Block := .branch 146 ![1267650600228229401496703205761, 146437906389534210, 4740813226943354771460, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B6891, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6890 : B6890.tree = HexagonCover.NBand.M8300_8500.SplitData.node6890 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6891
  · rfl
  · rfl

def B6889 : Block := .branch 161 ![1267650600228229401496703205761, 146437906389534210, 53273034739996541365262340, 1496577676626844588240652496863988076465268467982344, 649037107316853453566312041250832, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B6890]
theorem treeEq6889 : B6889.tree = HexagonCover.NBand.M8300_8500.SplitData.node6889 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6890

def B6888 : Block := .branch 170 ![1267650600228229401496703205761, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 3742905693226247029562492616565514864356231770275904] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6889, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1144).pointIds 1144)]
theorem treeEq6888 : B6888.tree = HexagonCover.NBand.M8300_8500.SplitData.node6888 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6889
  · rfl
  · rfl
  · rfl

def B6887 : Block := .branch 169 ![1267650600228229401496703205761, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 5731291558557666012491987528992454836008386592, 2994616854912824735442205982214777958292394308272192] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 587).pointIds 587), (.leaf 5 (Common.fact 1246).pointIds 1246), B6888]
theorem treeEq6887 : B6887.tree = HexagonCover.NBand.M8300_8500.SplitData.node6887 := by
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
  · exact treeEq6888

def B6886 : Block := .branch 125 ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 5731291516022370147374679596070628907037360160, 2994616866063197334707517552982637094616575061262400] ![(.leaf 0 (Common.fact 1076).pointIds 1076), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B6887, (.leaf 6 (Common.fact 1245).pointIds 1245)]
theorem treeEq6886 : B6886.tree = HexagonCover.NBand.M8300_8500.SplitData.node6886 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6887
  · rfl

def B6885 : Block := .branch 144 ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 5708990770823839524233143877797980545531379744, 2994616866063197334707517552982637094616575061262400] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B6886, (.leaf 6 (Common.fact 1244).pointIds 1244)]
theorem treeEq6885 : B6885.tree = HexagonCover.NBand.M8300_8500.SplitData.node6885 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6886
  · rfl

def B6884 : Block := .branch 152 ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2994616866063197334707517552982637094616575061262400] ![(.leaf 0 (Common.fact 301).pointIds 301), (.leaf 1 (Common.fact 302).pointIds 302), (.leaf 2 (Common.fact 303).pointIds 303), (.leaf 3 (Common.fact 304).pointIds 304), (.leaf 4 (Common.fact 305).pointIds 305), B6885, (.leaf 6 (Common.fact 1243).pointIds 1243)]
theorem treeEq6884 : B6884.tree = HexagonCover.NBand.M8300_8500.SplitData.node6884 := by
  change Tree.branch (152 : Fin 177) _ = Tree.branch (152 : Fin 177) _
  apply congrArg (Tree.branch (152 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6885
  · rfl

def B6883 : Block := .branch 160 ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B6884]
theorem treeEq6883 : B6883.tree = HexagonCover.NBand.M8300_8500.SplitData.node6883 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6884

theorem accepted6883 : B6883.accepted = true := by decide +kernel
theorem checked6883 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6883 (maskNeeds ![1267651204691139208811290558849, 146437906389534210, 53273034739996541365262340, 79228162514264337593543974920, 649037107316853453566312041250832, 393248, 2993155364425866431789313868149920811596919128719424]) := by
  rw [← treeEq6883]
  exact B6883.sound accepted6883
#print axioms checked6883

end HexagonCover.NBand.M8300_8500.SplitTree.Run0094
