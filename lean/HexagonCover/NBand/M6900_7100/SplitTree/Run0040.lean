import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0035
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0040
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0017_0028 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node0028 ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6900_7100.SplitTree.Run0035.checked0028
def B0027 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 9408126880630106637835381146273527510433808, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 162).pointIds 162), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 164).pointIds 164)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M6900_7100.SplitData.node0027 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0026 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0027, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M6900_7100.SplitData.node0026 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0027
  · rfl
  · rfl

def B0025 : Block := .branch 78 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B0026]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M6900_7100.SplitData.node0025 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0026

def B0024 : Block := .branch 65 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), B0025, (.leaf 3 (Common.fact 142).pointIds 142), (.leaf 4 (Common.fact 143).pointIds 143), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 145).pointIds 145)]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M6900_7100.SplitData.node0024 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0025
  · rfl
  · rfl
  · rfl
  · rfl

def B0023 : Block := .branch 138 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 3484491437270409865864955980101306485407760, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), B0024, (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 139).pointIds 139)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M6900_7100.SplitData.node0023 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024
  · rfl
  · rfl

def B0022 : Block := .branch 139 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0023, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 133).pointIds 133)]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M6900_7100.SplitData.node0022 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023
  · rfl
  · rfl

def B0021 : Block := .branch 140 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0022, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 127).pointIds 127)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M6900_7100.SplitData.node0021 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0022
  · rfl
  · rfl

def B0020 : Block := .branch 141 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0021, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 121).pointIds 121)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M6900_7100.SplitData.node0020 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl

def B0019 : Block := .branch 144 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), (.leaf 4 (Common.fact 114).pointIds 114), B0020, (.leaf 6 (Common.fact 115).pointIds 115)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M6900_7100.SplitData.node0019 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl

def B0018 : Block := .branch 89 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B0019]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M6900_7100.SplitData.node0018 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019

def B0017 : Block := .branch 55 ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 99).pointIds 99), B0018, Tip0017_0028, (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 103).pointIds 103)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M6900_7100.SplitData.node0017 := by
  change Tree.branch (55 : Fin 173) _ = Tree.branch (55 : Fin 173) _
  apply congrArg (Tree.branch (55 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0018
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0017 : B0017.accepted = true := by decide +kernel
theorem checked0017 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node0017 (maskNeeds ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0017]
  exact B0017.sound accepted0017
#print axioms checked0017

def B2976 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq2976 : B2976.tree = HexagonCover.NBand.M6900_7100.SplitData.node2976 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2975 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B2976, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq2975 : B2975.tree = HexagonCover.NBand.M6900_7100.SplitData.node2975 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2976
  · rfl
  · rfl
  · rfl

def B2974 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2975]
theorem treeEq2974 : B2974.tree = HexagonCover.NBand.M6900_7100.SplitData.node2974 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2975

def B2973 : Block := .branch 166 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B2974, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2973 : B2973.tree = HexagonCover.NBand.M6900_7100.SplitData.node2973 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2974
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2972 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2973, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2972 : B2972.tree = HexagonCover.NBand.M6900_7100.SplitData.node2972 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2973
  · rfl

def B2985 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq2985 : B2985.tree = HexagonCover.NBand.M6900_7100.SplitData.node2985 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2984 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B2985, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq2984 : B2984.tree = HexagonCover.NBand.M6900_7100.SplitData.node2984 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2985
  · rfl
  · rfl
  · rfl

def B2983 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2984]
theorem treeEq2983 : B2983.tree = HexagonCover.NBand.M6900_7100.SplitData.node2983 := by
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
  · exact treeEq2984

def B2982 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2983, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2982 : B2982.tree = HexagonCover.NBand.M6900_7100.SplitData.node2982 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2983
  · rfl
  · rfl

def B2981 : Block := .branch 132 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B2982]
theorem treeEq2981 : B2981.tree = HexagonCover.NBand.M6900_7100.SplitData.node2981 := by
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
  · exact treeEq2982

def B2980 : Block := .branch 133 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B2981]
theorem treeEq2980 : B2980.tree = HexagonCover.NBand.M6900_7100.SplitData.node2980 := by
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
  · exact treeEq2981

def B2979 : Block := .branch 157 ![385, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2980, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq2979 : B2979.tree = HexagonCover.NBand.M6900_7100.SplitData.node2979 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2980
  · rfl
  · rfl

def B2978 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144115188075857410, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2979, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq2978 : B2978.tree = HexagonCover.NBand.M6900_7100.SplitData.node2978 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2979
  · rfl

def B2977 : Block := .branch 169 ![10387129018270111715863986064851329, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B2978, (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq2977 : B2977.tree = HexagonCover.NBand.M6900_7100.SplitData.node2977 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2978
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2971 : Block := .branch 108 ![10387129018270111715863986064851329, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2972, (.leaf 5 (Common.fact 322).pointIds 322), B2977]
theorem treeEq2971 : B2971.tree = HexagonCover.NBand.M6900_7100.SplitData.node2971 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2972
  · rfl
  · exact treeEq2977

theorem accepted2971 : B2971.accepted = true := by decide +kernel
theorem checked2971 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2971 (maskNeeds ![10387129018270111715863986064851329, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2971]
  exact B2971.sound accepted2971
#print axioms checked2971

def Tip2968_2971 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2971 ![10387129018270111715863986064851329, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2971
def B2993 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq2993 : B2993.tree = HexagonCover.NBand.M6900_7100.SplitData.node2993 := by
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
  · rfl

def B2992 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2993, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq2992 : B2992.tree = HexagonCover.NBand.M6900_7100.SplitData.node2992 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2993
  · rfl
  · rfl

def B2991 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2992, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2991 : B2991.tree = HexagonCover.NBand.M6900_7100.SplitData.node2991 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2992
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2990 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2991]
theorem treeEq2990 : B2990.tree = HexagonCover.NBand.M6900_7100.SplitData.node2990 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2991

def B2989 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 648659083829708290, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2990]
theorem treeEq2989 : B2989.tree = HexagonCover.NBand.M6900_7100.SplitData.node2989 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2990

def B2988 : Block := .branch 171 ![2475880078570760549798248833, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2989, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1059).pointIds 1059)]
theorem treeEq2988 : B2988.tree = HexagonCover.NBand.M6900_7100.SplitData.node2988 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2989
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2987 : Block := .branch 151 ![2475880078570760549798248833, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2988, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2987 : B2987.tree = HexagonCover.NBand.M6900_7100.SplitData.node2987 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2988
  · rfl

def B2986 : Block := .branch 170 ![2475880078570760549798248833, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B2987, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq2986 : B2986.tree = HexagonCover.NBand.M6900_7100.SplitData.node2986 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2987
  · rfl
  · rfl

def B2970 : Block := .branch 101 ![10384596192949733827821542456689025, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip2968_2971, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2986]
theorem treeEq2970 : B2970.tree = HexagonCover.NBand.M6900_7100.SplitData.node2970 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2986

def B2995 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1062).pointIds 1062)]
theorem treeEq2995 : B2995.tree = HexagonCover.NBand.M6900_7100.SplitData.node2995 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2994 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B2995, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1061).pointIds 1061)]
theorem treeEq2994 : B2994.tree = HexagonCover.NBand.M6900_7100.SplitData.node2994 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2995
  · rfl
  · rfl
  · rfl

def B2969 : Block := .branch 91 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2970, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2994]
theorem treeEq2969 : B2969.tree = HexagonCover.NBand.M6900_7100.SplitData.node2969 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2970
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2994

def B3001 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1122433257491911512663687080580323301994847652020288] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1137).pointIds 1137)]
theorem treeEq3001 : B3001.tree = HexagonCover.NBand.M6900_7100.SplitData.node3001 := by
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
  · rfl

def B3000 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080580323301994847652020288] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3001, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 1136).pointIds 1136)]
theorem treeEq3000 : B3000.tree = HexagonCover.NBand.M6900_7100.SplitData.node3000 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3001
  · rfl
  · rfl

def B2999 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648659083829708290, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3000]
theorem treeEq2999 : B2999.tree = HexagonCover.NBand.M6900_7100.SplitData.node2999 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3000

def B2998 : Block := .branch 171 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543401065199606038621147639578688] ![B2999, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq2998 : B2998.tree = HexagonCover.NBand.M6900_7100.SplitData.node2998 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2997 : Block := .branch 151 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2998, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2997 : B2997.tree = HexagonCover.NBand.M6900_7100.SplitData.node2997 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2998
  · rfl

def B2996 : Block := .branch 170 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B2997, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq2996 : B2996.tree = HexagonCover.NBand.M6900_7100.SplitData.node2996 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2997
  · rfl
  · rfl

def B2968 : Block := .branch 89 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B2969, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2996]
theorem treeEq2968 : B2968.tree = HexagonCover.NBand.M6900_7100.SplitData.node2968 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2969
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2996

theorem accepted2968 : B2968.accepted = true := by decide +kernel
theorem checked2968 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2968 (maskNeeds ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2968]
  exact B2968.sound accepted2968
#print axioms checked2968

def B3025 : Block := .branch 161 ![385, 1538, 18446745173221185540, 5986310706507378352962293113491521476178833286651912, 98320, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1081).pointIds 1081), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq3025 : B3025.tree = HexagonCover.NBand.M6900_7100.SplitData.node3025 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3024 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1177).pointIds 1177), (.leaf 2 (Common.fact 1178).pointIds 1178), B3025, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq3024 : B3024.tree = HexagonCover.NBand.M6900_7100.SplitData.node3024 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3025
  · rfl
  · rfl
  · rfl

def B3023 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B3024]
theorem treeEq3023 : B3023.tree = HexagonCover.NBand.M6900_7100.SplitData.node3023 := by
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
  · exact treeEq3024

def B3033 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 1461501659108975050497766536840632538439393738816] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq3033 : B3033.tree = HexagonCover.NBand.M6900_7100.SplitData.node3033 := by
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

def B3032 : Block := .branch 151 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B3033, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3032 : B3032.tree = HexagonCover.NBand.M6900_7100.SplitData.node3032 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3033
  · rfl
  · rfl

def B3031 : Block := .branch 132 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B3032]
theorem treeEq3031 : B3031.tree = HexagonCover.NBand.M6900_7100.SplitData.node3031 := by
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
  · exact treeEq3032

def B3030 : Block := .branch 86 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920826709157852111578770551805025777794678848] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B3031, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq3030 : B3030.tree = HexagonCover.NBand.M6900_7100.SplitData.node3030 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3031
  · rfl
  · rfl
  · rfl

def B3029 : Block := .branch 133 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B3030]
theorem treeEq3029 : B3029.tree = HexagonCover.NBand.M6900_7100.SplitData.node3029 := by
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
  · exact treeEq3030

def B3028 : Block := .branch 157 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3029, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq3028 : B3028.tree = HexagonCover.NBand.M6900_7100.SplitData.node3028 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3029
  · rfl
  · rfl

def B3027 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3028, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq3027 : B3027.tree = HexagonCover.NBand.M6900_7100.SplitData.node3027 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3028
  · rfl

def B3026 : Block := .branch 160 ![10384593717070245552871351364092289, 906694581024491483170306, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 1181).pointIds 1181), (.leaf 2 (Common.fact 1166).pointIds 1166), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B3027]
theorem treeEq3026 : B3026.tree = HexagonCover.NBand.M6900_7100.SplitData.node3026 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3027

def B3022 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B3023, B3026, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq3022 : B3022.tree = HexagonCover.NBand.M6900_7100.SplitData.node3022 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3023
  · exact treeEq3026
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3036 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq3036 : B3036.tree = HexagonCover.NBand.M6900_7100.SplitData.node3036 := by
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
  · rfl

def B3035 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B3036, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq3035 : B3035.tree = HexagonCover.NBand.M6900_7100.SplitData.node3035 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3036
  · rfl
  · rfl

def B3034 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B3035, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq3034 : B3034.tree = HexagonCover.NBand.M6900_7100.SplitData.node3034 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3035
  · rfl

def B3021 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B3022, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B3034]
theorem treeEq3021 : B3021.tree = HexagonCover.NBand.M6900_7100.SplitData.node3021 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3022
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3034

def B3020 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B3021, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq3020 : B3020.tree = HexagonCover.NBand.M6900_7100.SplitData.node3020 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3019 : Block := .branch 169 ![10384593717070245552871351364092289, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B3020, (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3019 : B3019.tree = HexagonCover.NBand.M6900_7100.SplitData.node3019 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3020
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3018 : Block := .branch 109 ![10384593717070245552871351364092289, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B3019]
theorem treeEq3018 : B3018.tree = HexagonCover.NBand.M6900_7100.SplitData.node3018 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3019

def B3017 : Block := .branch 150 ![10384593717070245552871351364092289, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B3018, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq3017 : B3017.tree = HexagonCover.NBand.M6900_7100.SplitData.node3017 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3018
  · rfl
  · rfl

theorem accepted3017 : B3017.accepted = true := by decide +kernel
theorem checked3017 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node3017 (maskNeeds ![10384593717070245552871351364092289, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq3017]
  exact B3017.sound accepted3017
#print axioms checked3017

def Tip2966_2968 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2968 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2968
def B3007 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 931).pointIds 931)]
theorem treeEq3007 : B3007.tree = HexagonCover.NBand.M6900_7100.SplitData.node3007 := by
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
  · rfl

def B3006 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3007, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq3006 : B3006.tree = HexagonCover.NBand.M6900_7100.SplitData.node3006 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3007
  · rfl
  · rfl

def B3005 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648659083829708290, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400368858333940594743008821312] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3006]
theorem treeEq3005 : B3005.tree = HexagonCover.NBand.M6900_7100.SplitData.node3005 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3006

def B3004 : Block := .branch 171 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400678343343761939811733602368] ![B3005, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq3004 : B3004.tree = HexagonCover.NBand.M6900_7100.SplitData.node3004 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3003 : Block := .branch 151 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3004, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3003 : B3003.tree = HexagonCover.NBand.M6900_7100.SplitData.node3003 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3004
  · rfl

def B3002 : Block := .branch 170 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3003, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq3002 : B3002.tree = HexagonCover.NBand.M6900_7100.SplitData.node3002 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3003
  · rfl
  · rfl

def B2967 : Block := .branch 86 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip2966_2968, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B3002]
theorem treeEq2967 : B2967.tree = HexagonCover.NBand.M6900_7100.SplitData.node2967 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3002

def B3013 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq3013 : B3013.tree = HexagonCover.NBand.M6900_7100.SplitData.node3013 := by
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
  · rfl

def B3012 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080882554756898504945696832] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B3013, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq3012 : B3012.tree = HexagonCover.NBand.M6900_7100.SplitData.node3012 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3013
  · rfl
  · rfl

def B3011 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648659083829708290, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1180).pointIds 1180), (.leaf 2 (Common.fact 1174).pointIds 1174), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B3012]
theorem treeEq3011 : B3011.tree = HexagonCover.NBand.M6900_7100.SplitData.node3011 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3012

def B3010 : Block := .branch 171 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446531817850834667483693120] ![B3011, (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1076).pointIds 1076)]
theorem treeEq3010 : B3010.tree = HexagonCover.NBand.M6900_7100.SplitData.node3010 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3009 : Block := .branch 151 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B3010, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq3009 : B3009.tree = HexagonCover.NBand.M6900_7100.SplitData.node3009 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3010
  · rfl

def B3008 : Block := .branch 170 ![385, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1167).pointIds 1167), (.leaf 2 (Common.fact 1168).pointIds 1168), (.leaf 3 (Common.fact 658).pointIds 658), B3009, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq3008 : B3008.tree = HexagonCover.NBand.M6900_7100.SplitData.node3008 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3009
  · rfl
  · rfl

def B2966 : Block := .branch 78 ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), B2967, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B3008]
theorem treeEq2966 : B2966.tree = HexagonCover.NBand.M6900_7100.SplitData.node2966 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2967
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3008

theorem accepted2966 : B2966.accepted = true := by decide +kernel
theorem checked2966 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2966 (maskNeeds ![10384593717069655257060992658440577, 792774271905564162, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2966]
  exact B2966.sound accepted2966
#print axioms checked2966

end HexagonCover.NBand.M6900_7100.SplitTree.Run0040
