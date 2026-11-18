import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0095
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0096
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip6370_6374 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6374 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81406936983406606877366408994824, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] HexagonCover.NBand.M8300_8500.SplitTree.Run0095.checked6374
def Tip6370_6931 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6931 ![604462909807314587353473, 146437906389534210, 4840444091685460053596164, 79228162514264337593543974920, 98320, 393248, 2993155353275493832524003535322100960653013274853440] HexagonCover.NBand.M8300_8500.SplitTree.Run0095.checked6931
def B6930 : Block := .branch 120 ![385, 1538, 6148, 24584, 11150372599265311570767859136324180753088528, 393248, 2993155353275488515612177614043598588719684342251584] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1290).pointIds 1290)]
theorem treeEq6930 : B6930.tree = HexagonCover.NBand.M8300_8500.SplitData.node6930 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6929 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 2993155353275488515612177614043598588719684342251584] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B6930, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1289).pointIds 1289)]
theorem treeEq6929 : B6929.tree = HexagonCover.NBand.M8300_8500.SplitData.node6929 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6930
  · rfl
  · rfl

def B6928 : Block := .branch 144 ![385, 1538, 6148, 24584, 98320, 393248, 2993155353275488515612177614043598588719684342251584] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B6929, (.leaf 6 (Common.fact 1288).pointIds 1288)]
theorem treeEq6928 : B6928.tree = HexagonCover.NBand.M8300_8500.SplitData.node6928 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6929
  · rfl

def B6927 : Block := .branch 107 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 2993155353275493832524160753707090203947925463629888] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B6928, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1287).pointIds 1287)]
theorem treeEq6927 : B6927.tree = HexagonCover.NBand.M8300_8500.SplitData.node6927 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6928
  · rfl
  · rfl
  · rfl

def B6926 : Block := .branch 118 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 2993155353275493832524160753707090203947925463629888] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B6927, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1286).pointIds 1286)]
theorem treeEq6926 : B6926.tree = HexagonCover.NBand.M8300_8500.SplitData.node6926 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6927
  · rfl
  · rfl
  · rfl

def B6925 : Block := .branch 128 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 2993155353275493832524160753707090203947925463629888] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B6926, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1285).pointIds 1285)]
theorem treeEq6925 : B6925.tree = HexagonCover.NBand.M8300_8500.SplitData.node6925 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6926
  · rfl
  · rfl
  · rfl

def B6924 : Block := .branch 151 ![385, 1538, 6148, 24584, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524160753707090203947925463629888] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6925, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1284).pointIds 1284)]
theorem treeEq6924 : B6924.tree = HexagonCover.NBand.M8300_8500.SplitData.node6924 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6925
  · rfl
  · rfl

def B6923 : Block := .branch 168 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524160753707090203947925463629888] ![B6924, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1283).pointIds 1283)]
theorem treeEq6923 : B6923.tree = HexagonCover.NBand.M8300_8500.SplitData.node6923 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6924
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6373 : Block := .branch 97 ![1238544502195187589486477697, 151153343838634758899202, 53235255808133584203552772, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), Tip6370_6374, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B6923]
theorem treeEq6373 : B6373.tree = HexagonCover.NBand.M8300_8500.SplitData.node6373 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6923

def B6372 : Block := .branch 90 ![604462909807314587353473, 151153343838634758899202, 53235255808133584203552772, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![B6373, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), Tip6370_6931]
theorem treeEq6372 : B6372.tree = HexagonCover.NBand.M8300_8500.SplitData.node6372 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6373
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6952 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 16462354442917073859041229157041359523508848206282816] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1318).pointIds 1318)]
theorem treeEq6952 : B6952.tree = HexagonCover.NBand.M8300_8500.SplitData.node6952 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6951 : Block := .branch 174 ![604462909807314587353473, 151153199653077938865666, 33887701881072574053488644, 81169291181490041532719367741448, 178405961588244985132285746181186892047941648, 393248, 16462354442917073859041229157041359523508848206282816] ![(.leaf 0 (Common.fact 1314).pointIds 1314), (.leaf 1 (Common.fact 1255).pointIds 1255), (.leaf 2 (Common.fact 1315).pointIds 1315), (.leaf 3 (Common.fact 1316).pointIds 1316), B6952, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1317).pointIds 1317)]
theorem treeEq6951 : B6951.tree = HexagonCover.NBand.M8300_8500.SplitData.node6951 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6952
  · rfl
  · rfl

def B6950 : Block := .branch 173 ![604462909807314587353473, 151153199653077938865666, 33887701881072574053488644, 81169291181490041532719367741448, 178405961588244985132285746181186892047941648, 393248, 4489733029902317153116643007429569026487448814223424] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1312).pointIds 1312), (.leaf 3 (Common.fact 1313).pointIds 1313), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6951]
theorem treeEq6950 : B6950.tree = HexagonCover.NBand.M8300_8500.SplitData.node6950 := by
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
  · exact treeEq6951

def B6949 : Block := .branch 170 ![604462909807314587353473, 151153343838634758899202, 33892442694299517408253956, 81169291181490041532719367741448, 178405961588244985132285746181186892047941648, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6950]
theorem treeEq6949 : B6949.tree = HexagonCover.NBand.M8300_8500.SplitData.node6949 := by
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
  · exact treeEq6950

def B6371 : Block := .branch 85 ![604462909807314587353473, 151153343838634758899202, 33892442694299517408253956, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B6372, B6949, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq6371 : B6371.tree = HexagonCover.NBand.M8300_8500.SplitData.node6371 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6372
  · exact treeEq6949
  · rfl
  · rfl
  · rfl

def B6956 : Block := .branch 130 ![385, 1538, 6148, 81169252495863813864585777143816, 23945243004435475000094157431509327175229690832060432, 393248, 16462354442917073859041229157041359523508848206282816] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 1257).pointIds 1257), (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 1318).pointIds 1318)]
theorem treeEq6956 : B6956.tree = HexagonCover.NBand.M8300_8500.SplitData.node6956 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6955 : Block := .branch 174 ![604462909807314587353473, 151153199653077938865666, 14544888767238507258189828, 81248500001191192036246116392968, 178405961588244985132285746181186892047941648, 393248, 16462354442917073859041229157041359523508848206282816] ![(.leaf 0 (Common.fact 1314).pointIds 1314), (.leaf 1 (Common.fact 1255).pointIds 1255), (.leaf 2 (Common.fact 1321).pointIds 1321), (.leaf 3 (Common.fact 1322).pointIds 1322), B6956, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1317).pointIds 1317)]
theorem treeEq6955 : B6955.tree = HexagonCover.NBand.M8300_8500.SplitData.node6955 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6956
  · rfl
  · rfl

def B6954 : Block := .branch 173 ![604462909807314587353473, 151153199653077938865666, 14544888767238507258189828, 81248500001191192036246116392968, 178405961588244985132285746181186892047941648, 393248, 4489733029902317153116643007429569026487448814223424] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1319).pointIds 1319), (.leaf 3 (Common.fact 1320).pointIds 1320), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6955]
theorem treeEq6954 : B6954.tree = HexagonCover.NBand.M8300_8500.SplitData.node6954 := by
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
  · exact treeEq6955

def B6953 : Block := .branch 170 ![604462909807314587353473, 151153343838634758899202, 14549629580465450612955140, 81248500001191192036246116392968, 178405961588244985132285746181186892047941648, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), (.leaf 3 (Common.fact 831).pointIds 831), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B6954]
theorem treeEq6953 : B6953.tree = HexagonCover.NBand.M8300_8500.SplitData.node6953 := by
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
  · exact treeEq6954

def B6370 : Block := .branch 84 ![604462909807314587353473, 151153343838634758899202, 14549629580465450612955140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B6371, B6953, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6370 : B6370.tree = HexagonCover.NBand.M8300_8500.SplitData.node6370 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6371
  · exact treeEq6953
  · rfl
  · rfl
  · rfl

theorem accepted6370 : B6370.accepted = true := by decide +kernel
theorem checked6370 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6370 (maskNeeds ![604462909807314587353473, 151153343838634758899202, 14549629580465450612955140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216]) := by
  rw [← treeEq6370]
  exact B6370.sound accepted6370
#print axioms checked6370

def B6985 : Block := .branch 121 ![385, 1538, 6148, 24584, 11692102302308582201963921731530103965557020786704, 393248, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 885).pointIds 885), (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 1347).pointIds 1347)]
theorem treeEq6985 : B6985.tree = HexagonCover.NBand.M8300_8500.SplitData.node6985 := by
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

def B6984 : Block := .branch 163 ![385, 1538, 6148, 24584, 89203661358856334443069799839808309560442896, 393248, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B6985, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq6984 : B6984.tree = HexagonCover.NBand.M8300_8500.SplitData.node6984 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6985
  · rfl
  · rfl

def B6983 : Block := .branch 84 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B6984, (.leaf 3 (Common.fact 903).pointIds 903), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq6983 : B6983.tree = HexagonCover.NBand.M8300_8500.SplitData.node6983 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6984
  · rfl
  · rfl
  · rfl
  · rfl

def B6982 : Block := .branch 85 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B6983, (.leaf 3 (Common.fact 902).pointIds 902), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq6982 : B6982.tree = HexagonCover.NBand.M8300_8500.SplitData.node6982 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6983
  · rfl
  · rfl
  · rfl
  · rfl

def B6981 : Block := .branch 86 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89203661358856334443069799839808309560442896, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B6982, (.leaf 3 (Common.fact 892).pointIds 892), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 1346).pointIds 1346)]
theorem treeEq6981 : B6981.tree = HexagonCover.NBand.M8300_8500.SplitData.node6981 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6982
  · rfl
  · rfl
  · rfl
  · rfl

def B6980 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 882).pointIds 882), B6981, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1337).pointIds 1337)]
theorem treeEq6980 : B6980.tree = HexagonCover.NBand.M8300_8500.SplitData.node6980 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6981
  · rfl
  · rfl

def B6979 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89202980794122492566142873090593446024019984, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 881).pointIds 881), B6980, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6979 : B6979.tree = HexagonCover.NBand.M8300_8500.SplitData.node6979 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6980
  · rfl
  · rfl

def B6978 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89899879081576574539315864286613707321081872, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1336).pointIds 1336), B6979, (.leaf 0 [] 0)]
theorem treeEq6978 : B6978.tree = HexagonCover.NBand.M8300_8500.SplitData.node6978 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6979
  · rfl

def B6977 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 89899879081576574539315864286613707321081872, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1335).pointIds 1335), B6978, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6977 : B6977.tree = HexagonCover.NBand.M8300_8500.SplitData.node6977 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6978
  · rfl

def B6976 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573273537177090586191622856712, 696898287454081973172991196020261297160208, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 880).pointIds 880), B6977, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6976 : B6976.tree = HexagonCover.NBand.M8300_8500.SplitData.node6976 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6977
  · rfl
  · rfl

def B6975 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 4835703278458516698849288, 696898287454081973172991196020261297160208, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6976, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1334).pointIds 1334)]
theorem treeEq6975 : B6975.tree = HexagonCover.NBand.M8300_8500.SplitData.node6975 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6976
  · rfl
  · rfl
  · rfl

def B6974 : Block := .branch 172 ![385, 151153343838634758899202, 42519745089900516481028, 79232998217542796110242799624, 179102859875699067105458737377207153345003536, 393248, 38911019592319763950297760746217433166336936551907392] ![B6975, (.leaf 1 (Common.fact 1273).pointIds 1273), (.leaf 2 (Common.fact 1344).pointIds 1344), (.leaf 3 (Common.fact 1345).pointIds 1345), (.leaf 4 (Common.fact 1332).pointIds 1332), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1333).pointIds 1333)]
theorem treeEq6974 : B6974.tree = HexagonCover.NBand.M8300_8500.SplitData.node6974 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6975
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6973 : Block := .branch 174 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 79232998217542796110242799624, 179102859875699067105458737377207153345003536, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 1314).pointIds 1314), (.leaf 1 (Common.fact 1255).pointIds 1255), (.leaf 2 (Common.fact 1342).pointIds 1342), (.leaf 3 (Common.fact 1343).pointIds 1343), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B6974]
theorem treeEq6973 : B6973.tree = HexagonCover.NBand.M8300_8500.SplitData.node6973 := by
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
  · exact treeEq6974

def B6972 : Block := .branch 139 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81208871412824224491899247943688, 178405961588244985132285746181186892047941648, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B6973, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1326).pointIds 1326)]
theorem treeEq6972 : B6972.tree = HexagonCover.NBand.M8300_8500.SplitData.node6972 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6973
  · rfl
  · rfl

def B6971 : Block := .branch 148 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81208871412824224491899247943688, 178405961588244985132285746181186892047941648, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B6972, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1325).pointIds 1325)]
theorem treeEq6971 : B6971.tree = HexagonCover.NBand.M8300_8500.SplitData.node6971 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6972
  · rfl
  · rfl

def B6970 : Block := .branch 173 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81208871412824224491899247943688, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1340).pointIds 1340), (.leaf 3 (Common.fact 1341).pointIds 1341), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6971]
theorem treeEq6970 : B6970.tree = HexagonCover.NBand.M8300_8500.SplitData.node6970 := by
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
  · exact treeEq6971

theorem accepted6970 : B6970.accepted = true := by decide +kernel
theorem checked6970 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6970 (maskNeeds ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81208871412824224491899247943688, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216]) := by
  rw [← treeEq6970]
  exact B6970.sound accepted6970
#print axioms checked6970

def Tip6367_6370 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6370 ![604462909807314587353473, 151153343838634758899202, 14549629580465450612955140, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] checked6370
def Tip6367_6970 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6970 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81208871412824224491899247943688, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] checked6970
def B6969 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981458736490458600809542496976164192272, 393248, 38911019592297959294254904986238319115320097779482688] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 1339).pointIds 1339), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 1219).pointIds 1219)]
theorem treeEq6969 : B6969.tree = HexagonCover.NBand.M8300_8500.SplitData.node6969 := by
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

def B6968 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794122492566142873090593446024019984, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B6969, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 1338).pointIds 1338)]
theorem treeEq6968 : B6968.tree = HexagonCover.NBand.M8300_8500.SplitData.node6968 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6969
  · rfl
  · rfl

def B6967 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794122492566142873090593446024019984, 393248, 38911019592319742682649828187563466705423972066394176] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B6968, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 1337).pointIds 1337)]
theorem treeEq6967 : B6967.tree = HexagonCover.NBand.M8300_8500.SplitData.node6967 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6968
  · rfl
  · rfl

def B6966 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794122492566142873090593446024019984, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B6967, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 1077).pointIds 1077)]
theorem treeEq6966 : B6966.tree = HexagonCover.NBand.M8300_8500.SplitData.node6966 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6967
  · rfl
  · rfl

def B6965 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89899879081576574539315864286613707321081872, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 1336).pointIds 1336), B6966, (.leaf 0 [] 0)]
theorem treeEq6965 : B6965.tree = HexagonCover.NBand.M8300_8500.SplitData.node6965 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6966
  · rfl

def B6964 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89899879081576574539315864286613707321081872, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 1335).pointIds 1335), B6965, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq6964 : B6964.tree = HexagonCover.NBand.M8300_8500.SplitData.node6964 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6965
  · rfl

def B6963 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 696898287454081973172991196020261297160208, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B6964, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq6963 : B6963.tree = HexagonCover.NBand.M8300_8500.SplitData.node6963 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6964
  · rfl
  · rfl

def B6962 : Block := .branch 170 ![385, 146437906389534210, 4740813226943354771460, 9671406556917033397673992, 696898287454081973172991196020261297160208, 393248, 38911019592319763950297760746217433166336936551907392] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1060).pointIds 1060), (.leaf 2 (Common.fact 1061).pointIds 1061), B6963, (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 1334).pointIds 1334)]
theorem treeEq6962 : B6962.tree = HexagonCover.NBand.M8300_8500.SplitData.node6962 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6963
  · rfl
  · rfl
  · rfl

def B6961 : Block := .branch 172 ![385, 151153343838634758899202, 4878223023548417215305732, 79237833920821254626941624328, 179102859875699067105458737377207153345003536, 393248, 38911019592319763950297760746217433166336936551907392] ![B6962, (.leaf 1 (Common.fact 1273).pointIds 1273), (.leaf 2 (Common.fact 1330).pointIds 1330), (.leaf 3 (Common.fact 1331).pointIds 1331), (.leaf 4 (Common.fact 1332).pointIds 1332), (.leaf 5 (Common.fact 1239).pointIds 1239), (.leaf 6 (Common.fact 1333).pointIds 1333)]
theorem treeEq6961 : B6961.tree = HexagonCover.NBand.M8300_8500.SplitData.node6961 := by
  change Tree.branch (172 : Fin 177) _ = Tree.branch (172 : Fin 177) _
  apply congrArg (Tree.branch (172 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6962
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6960 : Block := .branch 174 ![604462909807314587353473, 151153343838634758899202, 4878223023548417215305732, 79237833920821254626941624328, 179102859875699067105458737377207153345003536, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 1314).pointIds 1314), (.leaf 1 (Common.fact 1255).pointIds 1255), (.leaf 2 (Common.fact 1327).pointIds 1327), (.leaf 3 (Common.fact 1328).pointIds 1328), (.leaf 4 (Common.fact 1329).pointIds 1329), (.leaf 5 (Common.fact 1241).pointIds 1241), B6961]
theorem treeEq6960 : B6960.tree = HexagonCover.NBand.M8300_8500.SplitData.node6960 := by
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
  · exact treeEq6961

def B6959 : Block := .branch 139 ![604462909807314587353473, 151153343838634758899202, 4878223023548417215305732, 81208876248527502950415946768392, 178405961588244985132285746181186892047941648, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B6960, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 1326).pointIds 1326)]
theorem treeEq6959 : B6959.tree = HexagonCover.NBand.M8300_8500.SplitData.node6959 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6960
  · rfl
  · rfl

def B6958 : Block := .branch 148 ![604462909807314587353473, 151153343838634758899202, 4878223023548417215305732, 81208876248527502950415946768392, 178405961588244985132285746181186892047941648, 393248, 14965776766290250538448588446993852172294137767788608] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B6959, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1325).pointIds 1325)]
theorem treeEq6958 : B6958.tree = HexagonCover.NBand.M8300_8500.SplitData.node6958 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6959
  · rfl
  · rfl

def B6957 : Block := .branch 173 ![604462909807314587353473, 151153343838634758899202, 4878223023548417215305732, 81208876248527502950415946768392, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1253).pointIds 1253), (.leaf 2 (Common.fact 1323).pointIds 1323), (.leaf 3 (Common.fact 1324).pointIds 1324), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6958]
theorem treeEq6957 : B6957.tree = HexagonCover.NBand.M8300_8500.SplitData.node6957 := by
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
  · exact treeEq6958

def B6369 : Block := .branch 83 ![604462909807314587353473, 151153343838634758899202, 4878223023548417215305732, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), Tip6367_6370, B6957, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq6369 : B6369.tree = HexagonCover.NBand.M8300_8500.SplitData.node6369 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6957
  · rfl
  · rfl
  · rfl

def B6368 : Block := .branch 82 ![604462909807314587353473, 151153343838634758899202, 42519745089900516481028, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), B6369, Tip6367_6970, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq6368 : B6368.tree = HexagonCover.NBand.M8300_8500.SplitData.node6368 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq6369
  · rfl
  · rfl
  · rfl
  · rfl

def B6989 : Block := .branch 120 ![385, 1538, 6148, 24584, 23945243004435475000094157431509327175229690832060432, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1355).pointIds 1355), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1356).pointIds 1356)]
theorem treeEq6989 : B6989.tree = HexagonCover.NBand.M8300_8500.SplitData.node6989 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6988 : Block := .branch 174 ![604462909807314587353473, 151116342193727538726402, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 11974082914673870997237713035769654370145479366803520] ![(.leaf 0 (Common.fact 1314).pointIds 1314), (.leaf 1 (Common.fact 1351).pointIds 1351), (.leaf 2 (Common.fact 1352).pointIds 1352), (.leaf 3 (Common.fact 1353).pointIds 1353), B6989, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1354).pointIds 1354)]
theorem treeEq6988 : B6988.tree = HexagonCover.NBand.M8300_8500.SplitData.node6988 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6989
  · rfl
  · rfl

def B6987 : Block := .branch 173 ![604462909807314587353473, 151116342193727538726402, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 1461501659114291313126886157863873124079974744128] ![(.leaf 0 (Common.fact 1311).pointIds 1311), (.leaf 1 (Common.fact 1348).pointIds 1348), (.leaf 2 (Common.fact 1349).pointIds 1349), (.leaf 3 (Common.fact 1350).pointIds 1350), (.leaf 4 (Common.fact 1254).pointIds 1254), (.leaf 5 (Common.fact 1238).pointIds 1238), B6988]
theorem treeEq6987 : B6987.tree = HexagonCover.NBand.M8300_8500.SplitData.node6987 := by
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
  · exact treeEq6988

def B6986 : Block := .branch 160 ![604462909807314587353473, 151116486379284358759938, 37815825351104580818948, 79228162514264337593543974920, 178405961588244985132285746181186892047941648, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 1065).pointIds 1065), (.leaf 2 (Common.fact 975).pointIds 975), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B6987]
theorem treeEq6986 : B6986.tree = HexagonCover.NBand.M8300_8500.SplitData.node6986 := by
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
  · exact treeEq6987

def B6367 : Block := .branch 65 ![604462909807314587353473, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 143).pointIds 143), B6368, B6986, (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 1068).pointIds 1068)]
theorem treeEq6367 : B6367.tree = HexagonCover.NBand.M8300_8500.SplitData.node6367 := by
  change Tree.branch (65 : Fin 177) _ = Tree.branch (65 : Fin 177) _
  apply congrArg (Tree.branch (65 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq6368
  · exact treeEq6986
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted6367 : B6367.accepted = true := by decide +kernel
theorem checked6367 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6367 (maskNeeds ![604462909807314587353473, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216]) := by
  rw [← treeEq6367]
  exact B6367.sound accepted6367
#print axioms checked6367

def Tip6364_6367 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node6367 ![604462909807314587353473, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 178405961588244985132285746181186892047941648, 393248, 2993155353275493832524002297382061675272738375729216] checked6367
def B6366 : Block := .branch 147 ![604462909807314587353473, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275493832524002297382061675272738375729216] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), Tip6364_6367, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1067).pointIds 1067)]
theorem treeEq6366 : B6366.tree = HexagonCover.NBand.M8300_8500.SplitData.node6366 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6365 : Block := .branch 124 ![604462909807314587353473, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![(.leaf 0 (Common.fact 1066).pointIds 1066), (.leaf 1 (Common.fact 104).pointIds 104), (.leaf 2 (Common.fact 105).pointIds 105), (.leaf 3 (Common.fact 106).pointIds 106), (.leaf 4 (Common.fact 107).pointIds 107), (.leaf 5 (Common.fact 108).pointIds 108), B6366]
theorem treeEq6365 : B6365.tree = HexagonCover.NBand.M8300_8500.SplitData.node6365 := by
  change Tree.branch (124 : Fin 177) _ = Tree.branch (124 : Fin 177) _
  apply congrArg (Tree.branch (124 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6366

def B7003 : Block := .branch 120 ![385, 1538, 6148, 24584, 16725558898897967356151788704486271129583632, 393248, 2993155353319028707841949862655870073918354808635456] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 1377).pointIds 1377), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 1378).pointIds 1378)]
theorem treeEq7003 : B7003.tree = HexagonCover.NBand.M8300_8500.SplitData.node7003 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7002 : Block := .branch 143 ![385, 1538, 6148, 24584, 5575186299632655785383929568162090376593424, 393248, 2993155353319028707841949862655870073918354808635456] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B7003, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 1376).pointIds 1376)]
theorem treeEq7002 : B7002.tree = HexagonCover.NBand.M8300_8500.SplitData.node7002 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7003
  · rfl
  · rfl

def B7001 : Block := .branch 135 ![385, 1538, 6148, 24584, 5575186299632655785383929568162090376593424, 748288838313422294120286634350736906063837462396960, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B7002]
theorem treeEq7001 : B7001.tree = HexagonCover.NBand.M8300_8500.SplitData.node7001 := by
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
  · exact treeEq7002

def B7000 : Block := .branch 169 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 2860070571711552417901955868467152363142086672, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 1056).pointIds 1056), (.leaf 1 (Common.fact 1057).pointIds 1057), (.leaf 2 (Common.fact 1058).pointIds 1058), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 1374).pointIds 1374), B7001, (.leaf 6 (Common.fact 1375).pointIds 1375)]
theorem treeEq7000 : B7000.tree = HexagonCover.NBand.M8300_8500.SplitData.node7000 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7001
  · rfl

def B6999 : Block := .branch 142 ![385, 146437906389534210, 4740813226943354771460, 79228162514264337593543974920, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 282).pointIds 282), (.leaf 1 (Common.fact 283).pointIds 283), (.leaf 2 (Common.fact 284).pointIds 284), (.leaf 3 (Common.fact 285).pointIds 285), B7000, (.leaf 5 (Common.fact 286).pointIds 286), (.leaf 6 (Common.fact 1373).pointIds 1373)]
theorem treeEq6999 : B6999.tree = HexagonCover.NBand.M8300_8500.SplitData.node6999 := by
  change Tree.branch (142 : Fin 177) _ = Tree.branch (142 : Fin 177) _
  apply congrArg (Tree.branch (142 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7000
  · rfl
  · rfl

def B6998 : Block := .branch 147 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 109).pointIds 109), (.leaf 1 (Common.fact 110).pointIds 110), (.leaf 2 (Common.fact 111).pointIds 111), (.leaf 3 (Common.fact 112).pointIds 112), B6999, (.leaf 5 (Common.fact 113).pointIds 113), (.leaf 6 (Common.fact 1372).pointIds 1372)]
theorem treeEq6998 : B6998.tree = HexagonCover.NBand.M8300_8500.SplitData.node6998 := by
  change Tree.branch (147 : Fin 177) _ = Tree.branch (147 : Fin 177) _
  apply congrArg (Tree.branch (147 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6999
  · rfl
  · rfl

def B6997 : Block := .branch 148 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B6998, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 1371).pointIds 1371)]
theorem treeEq6997 : B6997.tree = HexagonCover.NBand.M8300_8500.SplitData.node6997 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6998
  · rfl
  · rfl

def B6996 : Block := .branch 149 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 1365).pointIds 1365), (.leaf 1 (Common.fact 1366).pointIds 1366), (.leaf 2 (Common.fact 1367).pointIds 1367), (.leaf 3 (Common.fact 1368).pointIds 1368), B6997, (.leaf 5 (Common.fact 1369).pointIds 1369), (.leaf 6 (Common.fact 1370).pointIds 1370)]
theorem treeEq6996 : B6996.tree = HexagonCover.NBand.M8300_8500.SplitData.node6996 := by
  change Tree.branch (149 : Fin 177) _ = Tree.branch (149 : Fin 177) _
  apply congrArg (Tree.branch (149 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6997
  · rfl
  · rfl

def B6995 : Block := .branch 150 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 786).pointIds 786), (.leaf 1 (Common.fact 787).pointIds 787), (.leaf 2 (Common.fact 788).pointIds 788), (.leaf 3 (Common.fact 789).pointIds 789), B6996, (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 1364).pointIds 1364)]
theorem treeEq6995 : B6995.tree = HexagonCover.NBand.M8300_8500.SplitData.node6995 := by
  change Tree.branch (150 : Fin 177) _ = Tree.branch (150 : Fin 177) _
  apply congrArg (Tree.branch (150 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6996
  · rfl
  · rfl

def B6994 : Block := .branch 107 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B6995, (.leaf 4 (Common.fact 1362).pointIds 1362), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 1363).pointIds 1363)]
theorem treeEq6994 : B6994.tree = HexagonCover.NBand.M8300_8500.SplitData.node6994 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6995
  · rfl
  · rfl
  · rfl

def B6993 : Block := .branch 118 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B6994, (.leaf 4 (Common.fact 1360).pointIds 1360), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 1361).pointIds 1361)]
theorem treeEq6993 : B6993.tree = HexagonCover.NBand.M8300_8500.SplitData.node6993 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6994
  · rfl
  · rfl
  · rfl

def B6992 : Block := .branch 128 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 2854495385411919762116571938898990272765591568, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B6993, (.leaf 4 (Common.fact 1358).pointIds 1358), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 1359).pointIds 1359)]
theorem treeEq6992 : B6992.tree = HexagonCover.NBand.M8300_8500.SplitData.node6992 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq6993
  · rfl
  · rfl
  · rfl

def B6991 : Block := .branch 151 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069739332558124167088477569088] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B6992, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 1357).pointIds 1357)]
theorem treeEq6991 : B6991.tree = HexagonCover.NBand.M8300_8500.SplitData.node6991 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6992
  · rfl
  · rfl

def B6990 : Block := .branch 168 ![385, 146437906389534210, 4740813226943354771460, 81208866577120946033382549118984, 98320, 393248, 2993155353275472564876069739332558124167088477569088] ![B6991, (.leaf 1 (Common.fact 1013).pointIds 1013), (.leaf 2 (Common.fact 1014).pointIds 1014), (.leaf 3 (Common.fact 946).pointIds 946), (.leaf 4 (Common.fact 1015).pointIds 1015), (.leaf 5 (Common.fact 561).pointIds 561), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq6990 : B6990.tree = HexagonCover.NBand.M8300_8500.SplitData.node6990 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6991
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B6364 : Block := .branch 79 ![385, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000] ![B6365, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), B6990]
theorem treeEq6364 : B6364.tree = HexagonCover.NBand.M8300_8500.SplitData.node6364 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq6365
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq6990

theorem accepted6364 : B6364.accepted = true := by decide +kernel
theorem checked6364 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node6364 (maskNeeds ![385, 151116486379284358759938, 42519745089900516481028, 81248480658378078202179321094152, 98320, 393248, 2993155353275472564876069738728095214359773890216000]) := by
  rw [← treeEq6364]
  exact B6364.sound accepted6364
#print axioms checked6364

end HexagonCover.NBand.M8300_8500.SplitTree.Run0096
