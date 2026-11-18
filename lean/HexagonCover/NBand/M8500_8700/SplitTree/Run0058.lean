import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.NBand.M8500_8700.SplitTree.Run0054
import HexagonCover.NBand.M8500_8700.SplitTree.Run0057
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0058
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def Tip3623_3627 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3627 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0054.checked3627
def B3896 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq3896 : B3896.tree = HexagonCover.NBand.M8500_8700.SplitData.node3896 := by
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
  · rfl

def B3895 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3896, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq3895 : B3895.tree = HexagonCover.NBand.M8500_8700.SplitData.node3895 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3896
  · rfl

def B3894 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3895]
theorem treeEq3894 : B3894.tree = HexagonCover.NBand.M8500_8700.SplitData.node3894 := by
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
  · exact treeEq3895

def B3626 : Block := .branch 84 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip3623_3627, B3894, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq3626 : B3626.tree = HexagonCover.NBand.M8500_8700.SplitData.node3626 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3894
  · rfl
  · rfl
  · rfl

def B3899 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq3899 : B3899.tree = HexagonCover.NBand.M8500_8700.SplitData.node3899 := by
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
  · rfl

def B3898 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B3899, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq3898 : B3898.tree = HexagonCover.NBand.M8500_8700.SplitData.node3898 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3899
  · rfl

def B3897 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3898]
theorem treeEq3897 : B3897.tree = HexagonCover.NBand.M8500_8700.SplitData.node3897 := by
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
  · exact treeEq3898

def B3625 : Block := .branch 83 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B3626, B3897, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq3625 : B3625.tree = HexagonCover.NBand.M8500_8700.SplitData.node3625 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3626
  · exact treeEq3897
  · rfl
  · rfl
  · rfl

def B3904 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq3904 : B3904.tree = HexagonCover.NBand.M8500_8700.SplitData.node3904 := by
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

def B3903 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), B3904, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq3903 : B3903.tree = HexagonCover.NBand.M8500_8700.SplitData.node3903 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3904
  · rfl

def B3902 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B3903]
theorem treeEq3902 : B3902.tree = HexagonCover.NBand.M8500_8700.SplitData.node3902 := by
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
  · exact treeEq3903

def B3901 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3902, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq3901 : B3901.tree = HexagonCover.NBand.M8500_8700.SplitData.node3901 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3902
  · rfl
  · rfl
  · rfl

def B3900 : Block := .branch 161 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 960).pointIds 960), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B3901]
theorem treeEq3900 : B3900.tree = HexagonCover.NBand.M8500_8700.SplitData.node3900 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3901

def B3624 : Block := .branch 82 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B3625, B3900, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq3624 : B3624.tree = HexagonCover.NBand.M8500_8700.SplitData.node3624 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3625
  · exact treeEq3900
  · rfl
  · rfl
  · rfl

def B3907 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq3907 : B3907.tree = HexagonCover.NBand.M8500_8700.SplitData.node3907 := by
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

def B3906 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B3907, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq3906 : B3906.tree = HexagonCover.NBand.M8500_8700.SplitData.node3906 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3907
  · rfl
  · rfl
  · rfl

def B3905 : Block := .branch 160 ![1237940039287632074712809857, 528905046152318763927042, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B3906]
theorem treeEq3905 : B3905.tree = HexagonCover.NBand.M8500_8700.SplitData.node3905 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3906

def B3623 : Block := .branch 78 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B3624, B3905, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq3623 : B3623.tree = HexagonCover.NBand.M8500_8700.SplitData.node3623 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3624
  · exact treeEq3905
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3623 : B3623.accepted = true := by decide +kernel
theorem checked3623 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3623 (maskNeeds ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq3623]
  exact B3623.sound accepted3623
#print axioms checked3623

def Tip3622_3912 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3912 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] HexagonCover.NBand.M8500_8700.SplitTree.Run0057.checked3912
def Tip3622_3623 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node3623 ![1237940039287632074712809857, 226673591248661470250498, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] checked3623
def B4181 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq4181 : B4181.tree = HexagonCover.NBand.M8500_8700.SplitData.node4181 := by
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
  · rfl

def B4180 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4181, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq4180 : B4180.tree = HexagonCover.NBand.M8500_8700.SplitData.node4180 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4181
  · rfl

def B4179 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158475667841642509253883224072, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 883).pointIds 883), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4180]
theorem treeEq4179 : B4179.tree = HexagonCover.NBand.M8500_8700.SplitData.node4179 := by
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
  · exact treeEq4180

def B3911 : Block := .branch 84 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), Tip3622_3912, B4179, (.leaf 4 (Common.fact 252).pointIds 252), (.leaf 5 (Common.fact 253).pointIds 253), (.leaf 6 (Common.fact 254).pointIds 254)]
theorem treeEq3911 : B3911.tree = HexagonCover.NBand.M8500_8700.SplitData.node3911 := by
  change Tree.branch (84 : Fin 175) _ = Tree.branch (84 : Fin 175) _
  apply congrArg (Tree.branch (84 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4179
  · rfl
  · rfl
  · rfl

def B4184 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 797).pointIds 797)]
theorem treeEq4184 : B4184.tree = HexagonCover.NBand.M8500_8700.SplitData.node4184 := by
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
  · rfl

def B4183 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2993155364447660454008203348802051632157275658387520] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4184, (.leaf 6 (Common.fact 793).pointIds 793)]
theorem treeEq4183 : B4183.tree = HexagonCover.NBand.M8500_8700.SplitData.node4183 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4184
  · rfl

def B4182 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158465996435085592220485574664, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 813).pointIds 813), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4183]
theorem treeEq4182 : B4182.tree = HexagonCover.NBand.M8500_8700.SplitData.node4182 := by
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
  · exact treeEq4183

def B3910 : Block := .branch 83 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 245).pointIds 245), (.leaf 1 (Common.fact 246).pointIds 246), B3911, B4182, (.leaf 4 (Common.fact 247).pointIds 247), (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 249).pointIds 249)]
theorem treeEq3910 : B3910.tree = HexagonCover.NBand.M8500_8700.SplitData.node3910 := by
  change Tree.branch (83 : Fin 175) _ = Tree.branch (83 : Fin 175) _
  apply congrArg (Tree.branch (83 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3911
  · exact treeEq4182
  · rfl
  · rfl
  · rfl

def B4189 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 748288838313422294120286634350736906063837462396960, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq4189 : B4189.tree = HexagonCover.NBand.M8500_8700.SplitData.node4189 := by
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

def B4188 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 2996078367722322259844610718467484198196587523473472] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), B4189, (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq4188 : B4188.tree = HexagonCover.NBand.M8500_8700.SplitData.node4188 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4189
  · rfl

def B4187 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962451535966627055644403482779656, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 824).pointIds 824), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4188]
theorem treeEq4187 : B4187.tree = HexagonCover.NBand.M8500_8700.SplitData.node4187 := by
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
  · exact treeEq4188

def B4186 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4187, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq4186 : B4186.tree = HexagonCover.NBand.M8500_8700.SplitData.node4186 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4187
  · rfl
  · rfl
  · rfl

def B4185 : Block := .branch 161 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158461160731807133703786749960, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), (.leaf 2 (Common.fact 960).pointIds 960), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B4186]
theorem treeEq4185 : B4185.tree = HexagonCover.NBand.M8500_8700.SplitData.node4185 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4186

def B3909 : Block := .branch 82 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), B3910, B4185, (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 0 [] 0)]
theorem treeEq3909 : B3909.tree = HexagonCover.NBand.M8500_8700.SplitData.node3909 := by
  change Tree.branch (82 : Fin 175) _ = Tree.branch (82 : Fin 175) _
  apply congrArg (Tree.branch (82 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3910
  · exact treeEq4185
  · rfl
  · rfl
  · rfl

def B4192 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706507378352962293074805895248510699696054280, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq4192 : B4192.tree = HexagonCover.NBand.M8500_8700.SplitData.node4192 := by
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

def B4191 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4192, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 779).pointIds 779)]
theorem treeEq4191 : B4191.tree = HexagonCover.NBand.M8500_8700.SplitData.node4191 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4192
  · rfl
  · rfl
  · rfl

def B4190 : Block := .branch 160 ![1237940039287632074712809857, 453384075914551859611138, 37778967891754180679684, 24584, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), (.leaf 1 (Common.fact 899).pointIds 899), (.leaf 2 (Common.fact 959).pointIds 959), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B4191]
theorem treeEq4190 : B4190.tree = HexagonCover.NBand.M8500_8700.SplitData.node4190 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4191

def B3908 : Block := .branch 78 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![B3909, B4190, (.leaf 2 (Common.fact 236).pointIds 236), (.leaf 3 (Common.fact 237).pointIds 237), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq3908 : B3908.tree = HexagonCover.NBand.M8500_8700.SplitData.node3908 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq3909
  · exact treeEq4190
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3622 : Block := .branch 76 ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752] ![(.leaf 0 (Common.fact 231).pointIds 231), Tip3622_3623, B3908, (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 235).pointIds 235)]
theorem treeEq3622 : B3622.tree = HexagonCover.NBand.M8500_8700.SplitData.node3622 := by
  change Tree.branch (76 : Fin 175) _ = Tree.branch (76 : Fin 175) _
  apply congrArg (Tree.branch (76 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3908
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3622 : B3622.accepted = true := by decide +kernel
theorem checked3622 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node3622 (maskNeeds ![1237940039287632074712809857, 151152621010894565934594, 37797414635827890231300, 237684487542793012780631875592, 1393797904136159731261855295847582874566672, 393248, 11226643701663450043555079585443616680050752]) := by
  rw [← treeEq3622]
  exact B3622.sound accepted3622
#print axioms checked3622

def B4224 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq4224 : B4224.tree = HexagonCover.NBand.M8500_8700.SplitData.node4224 := by
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
  · rfl

def B4223 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4224, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq4223 : B4223.tree = HexagonCover.NBand.M8500_8700.SplitData.node4223 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4224
  · rfl

def B4222 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4223]
theorem treeEq4222 : B4222.tree = HexagonCover.NBand.M8500_8700.SplitData.node4222 := by
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
  · exact treeEq4223

def B4221 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4222, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq4221 : B4221.tree = HexagonCover.NBand.M8500_8700.SplitData.node4221 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4222
  · rfl
  · rfl
  · rfl

def B4220 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 22300745198530623141535718272648361506373664, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 517).pointIds 517), B4221]
theorem treeEq4220 : B4220.tree = HexagonCover.NBand.M8500_8700.SplitData.node4220 := by
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
  · exact treeEq4221

def B4226 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689650974042447903871204520386568, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), (.leaf 6 (Common.fact 567).pointIds 567)]
theorem treeEq4226 : B4226.tree = HexagonCover.NBand.M8500_8700.SplitData.node4226 := by
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

def B4225 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727357899236552655360504824356872, 1329227995784915872903807060280442896, 393248, 33451160333091799829611510330799020985286720] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4226, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 570).pointIds 570)]
theorem treeEq4225 : B4225.tree = HexagonCover.NBand.M8500_8700.SplitData.node4225 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4226
  · rfl
  · rfl
  · rfl

def B4219 : Block := .branch 144 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), B4220, B4225]
theorem treeEq4219 : B4219.tree = HexagonCover.NBand.M8500_8700.SplitData.node4219 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4220
  · exact treeEq4225

def B4232 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq4232 : B4232.tree = HexagonCover.NBand.M8500_8700.SplitData.node4232 := by
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
  · rfl

def B4231 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299789179515365405137334053416731525355794858048] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4232, (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq4231 : B4231.tree = HexagonCover.NBand.M8500_8700.SplitData.node4231 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4232
  · rfl

def B4230 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706855827496689809430367476432546391608287240, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 578).pointIds 578), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4231]
theorem treeEq4230 : B4230.tree = HexagonCover.NBand.M8500_8700.SplitData.node4230 := by
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
  · exact treeEq4231

def B4229 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 393248, 374144435925826188923990796650469107270005946843200] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4230, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 577).pointIds 577)]
theorem treeEq4229 : B4229.tree = HexagonCover.NBand.M8500_8700.SplitData.node4229 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4230
  · rfl
  · rfl
  · rfl

def B4228 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 16769115041863847479475100654238087215841344] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4229]
theorem treeEq4228 : B4228.tree = HexagonCover.NBand.M8500_8700.SplitData.node4228 := by
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
  · exact treeEq4229

def B4227 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 16769157577159712596783033576064016186867776] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4228, (.leaf 6 (Common.fact 571).pointIds 571)]
theorem treeEq4227 : B4227.tree = HexagonCover.NBand.M8500_8700.SplitData.node4227 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4228
  · rfl

def B4218 : Block := .branch 142 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B4219, (.leaf 5 (Common.fact 339).pointIds 339), B4227]
theorem treeEq4218 : B4218.tree = HexagonCover.NBand.M8500_8700.SplitData.node4218 := by
  change Tree.branch (142 : Fin 175) _ = Tree.branch (142 : Fin 175) _
  apply congrArg (Tree.branch (142 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4219
  · rfl
  · exact treeEq4227

theorem accepted4218 : B4218.accepted = true := by decide +kernel
theorem checked4218 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4218 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq4218]
  exact B4218.sound accepted4218
#print axioms checked4218

def Tip4215_4218 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node4218 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 348449143727516355561581184035691912257544, 1393797904136159731261855295847582874566672, 393248, 11193971277527056811399104007901925810372672] checked4218
def B4237 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq4237 : B4237.tree = HexagonCover.NBand.M8500_8700.SplitData.node4237 := by
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
  · rfl

def B4236 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4237, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq4236 : B4236.tree = HexagonCover.NBand.M8500_8700.SplitData.node4236 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4237
  · rfl

def B4235 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 589).pointIds 589), (.leaf 5 (Common.fact 387).pointIds 387), B4236]
theorem treeEq4235 : B4235.tree = HexagonCover.NBand.M8500_8700.SplitData.node4235 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4236

def B4234 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 588).pointIds 588), B4235, (.leaf 0 [] 0)]
theorem treeEq4234 : B4234.tree = HexagonCover.NBand.M8500_8700.SplitData.node4234 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4235
  · rfl

def B4233 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 353894991474808894234635949102411261509648, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 587).pointIds 587), B4234, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4233 : B4233.tree = HexagonCover.NBand.M8500_8700.SplitData.node4233 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4234
  · rfl

def B4217 : Block := .branch 138 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1399242422655931853994122743132803207102480, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip4215_4218, B4233, (.leaf 5 (Common.fact 333).pointIds 333), (.leaf 6 (Common.fact 334).pointIds 334)]
theorem treeEq4217 : B4217.tree = HexagonCover.NBand.M8500_8700.SplitData.node4217 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4233
  · rfl
  · rfl

def B4243 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1496577676626844588240573268701473812127674924400672, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq4243 : B4243.tree = HexagonCover.NBand.M8500_8700.SplitData.node4243 := by
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
  · rfl

def B4242 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783609773583643216564084901157082173709746240] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4243, (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq4242 : B4242.tree = HexagonCover.NBand.M8500_8700.SplitData.node4242 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4243
  · rfl

def B4241 : Block := .branch 171 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 5986310706508058917696610320707907583751124496179208, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 933).pointIds 933), (.leaf 1 (Common.fact 953).pointIds 953), (.leaf 2 (Common.fact 954).pointIds 954), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 745).pointIds 745), (.leaf 5 (Common.fact 566).pointIds 566), B4242]
theorem treeEq4241 : B4241.tree = HexagonCover.NBand.M8500_8700.SplitData.node4241 := by
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
  · exact treeEq4242

def B4240 : Block := .branch 172 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 393248, 374144430356084407162070026681953532826823861731392] ![(.leaf 0 (Common.fact 931).pointIds 931), (.leaf 1 (Common.fact 951).pointIds 951), (.leaf 2 (Common.fact 952).pointIds 952), B4241, (.leaf 4 (Common.fact 742).pointIds 742), (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 607).pointIds 607)]
theorem treeEq4240 : B4240.tree = HexagonCover.NBand.M8500_8700.SplitData.node4240 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4241
  · rfl
  · rfl
  · rfl

def B4239 : Block := .branch 168 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1329227995784915872903807060280442896, 5708990770823839524233143877797980545531379744, 11199373260101926709506585079794905130729536] ![(.leaf 0 (Common.fact 940).pointIds 940), (.leaf 1 (Common.fact 949).pointIds 949), (.leaf 2 (Common.fact 950).pointIds 950), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 574).pointIds 574), B4240]
theorem treeEq4239 : B4239.tree = HexagonCover.NBand.M8500_8700.SplitData.node4239 := by
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
  · exact treeEq4240

def B4238 : Block := .branch 152 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904136159731261855295847582874566672, 393248, 11199415795397791826814518001620834101755968] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B4239, (.leaf 6 (Common.fact 602).pointIds 602)]
theorem treeEq4238 : B4238.tree = HexagonCover.NBand.M8500_8700.SplitData.node4238 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4239
  · rfl

def B4216 : Block := .branch 132 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 680564734317245902012335240424800149512, 1393797904785196838578708749413894915719184, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B4217, (.leaf 5 (Common.fact 329).pointIds 329), B4238]
theorem treeEq4216 : B4216.tree = HexagonCover.NBand.M8500_8700.SplitData.node4216 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4217
  · rfl
  · exact treeEq4238

def B4248 : Block := .branch 169 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 1730417938599789055153162841936079095272624131276832, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 937).pointIds 937), (.leaf 1 (Common.fact 957).pointIds 957), (.leaf 2 (Common.fact 958).pointIds 958), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 754).pointIds 754), (.leaf 5 (Common.fact 687).pointIds 687), (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq4248 : B4248.tree = HexagonCover.NBand.M8500_8700.SplitData.node4248 := by
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
  · rfl

def B4247 : Block := .branch 170 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 1329227995784915872903807060280442896, 233840261972944466912589573234605283144949207269408, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 935).pointIds 935), (.leaf 1 (Common.fact 955).pointIds 955), (.leaf 2 (Common.fact 956).pointIds 956), (.leaf 3 (Common.fact 748).pointIds 748), (.leaf 4 (Common.fact 749).pointIds 749), B4248, (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq4247 : B4247.tree = HexagonCover.NBand.M8500_8700.SplitData.node4247 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4248
  · rfl

def B4246 : Block := .branch 163 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 233840261972944466912589573234605283144949207269408, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 618).pointIds 618), (.leaf 5 (Common.fact 387).pointIds 387), B4247]
theorem treeEq4246 : B4246.tree = HexagonCover.NBand.M8500_8700.SplitData.node4246 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4247

def B4245 : Block := .branch 165 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 187072209578355573530071658587684226515959365894176, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 617).pointIds 617), B4246, (.leaf 0 [] 0)]
theorem treeEq4245 : B4245.tree = HexagonCover.NBand.M8500_8700.SplitData.node4245 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4246
  · rfl

def B4244 : Block := .branch 167 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 158456325028528675187087925256, 684553066866338991398914202356418707472, 393248, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 538).pointIds 538), (.leaf 1 (Common.fact 539).pointIds 539), (.leaf 2 (Common.fact 540).pointIds 540), (.leaf 3 (Common.fact 541).pointIds 541), (.leaf 4 (Common.fact 616).pointIds 616), B4245, (.leaf 6 (Common.fact 543).pointIds 543)]
theorem treeEq4244 : B4244.tree = HexagonCover.NBand.M8500_8700.SplitData.node4244 := by
  change Tree.branch (167 : Fin 175) _ = Tree.branch (167 : Fin 175) _
  apply congrArg (Tree.branch (167 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4245
  · rfl

def B4215 : Block := .branch 129 ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), (.leaf 2 (Common.fact 322).pointIds 322), B4216, B4244, (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq4215 : B4215.tree = HexagonCover.NBand.M8500_8700.SplitData.node4215 := by
  change Tree.branch (129 : Fin 175) _ = Tree.branch (129 : Fin 175) _
  apply congrArg (Tree.branch (129 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4216
  · exact treeEq4244
  · rfl
  · rfl

theorem accepted4215 : B4215.accepted = true := by decide +kernel
theorem checked4215 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node4215 (maskNeeds ![1237940039287632074712809857, 151115727522747146831362, 37778967891754180679684, 475368975085586025561263726600, 1393800563241188408410454557028015476408336, 393248, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq4215]
  exact B4215.sound accepted4215
#print axioms checked4215

end HexagonCover.NBand.M8500_8700.SplitTree.Run0058
