import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0000
import HexagonCover.NBand.M7300_7500.SplitTree.Run0032
import HexagonCover.NBand.M7300_7500.SplitTree.Run0035
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0041
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0014_0033 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0033 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 93536104789220322060900946601775035083908654170144, 21778071483891109096836968272374173007936] HexagonCover.NBand.M7300_7500.SplitTree.Run0000.checked0033
def Tip0014_0073 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0073 ![385, 360289069701268994, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] HexagonCover.NBand.M7300_7500.SplitTree.Run0032.checked0073
def Tip0014_2318 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2318 ![385, 144257025075840514, 18554830464766449668, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] HexagonCover.NBand.M7300_7500.SplitTree.Run0035.checked2318
def B0025 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 9408126880630106637835381146273527510433808, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 152).pointIds 152)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M7300_7500.SplitData.node0025 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0024 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B0025, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 145).pointIds 145)]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M7300_7500.SplitData.node0024 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0025
  · rfl
  · rfl

def B0023 : Block := .branch 78 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B0024]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M7300_7500.SplitData.node0023 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024

def B0022 : Block := .branch 144 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B0023, (.leaf 6 (Common.fact 133).pointIds 133)]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M7300_7500.SplitData.node0022 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023
  · rfl

def B0021 : Block := .branch 87 ![385, 180145084606449154, 36893488147419109380, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257593281732674916694546186304] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B0022]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M7300_7500.SplitData.node0021 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0022

def B0020 : Block := .branch 65 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B0021, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 121).pointIds 121)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M7300_7500.SplitData.node0020 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl
  · rfl
  · rfl

def B0019 : Block := .branch 138 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 3484491437270409865864955980101306485407760, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0020, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 115).pointIds 115)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M7300_7500.SplitData.node0019 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl

def B0018 : Block := .branch 139 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0019, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 109).pointIds 109)]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M7300_7500.SplitData.node0018 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019
  · rfl
  · rfl

def B0017 : Block := .branch 140 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 2787593149816327892691964784081045188345872, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0018, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 103).pointIds 103)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M7300_7500.SplitData.node0017 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018
  · rfl
  · rfl

def B0016 : Block := .branch 141 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), B0017, (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 97).pointIds 97)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M7300_7500.SplitData.node0016 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0017
  · rfl
  · rfl

def B0015 : Block := .branch 89 ![385, 180145084606449154, 6148, 79266848140492005727134572552, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 86).pointIds 86), (.leaf 1 (Common.fact 87).pointIds 87), (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B0016]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M7300_7500.SplitData.node0015 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0016

def B0032 : Block := .branch 166 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 32667107225361139927664955710190755774528] ![(.leaf 0 (Common.fact 186).pointIds 186), (.leaf 1 (Common.fact 187).pointIds 187), (.leaf 2 (Common.fact 188).pointIds 188), (.leaf 3 (Common.fact 189).pointIds 189), (.leaf 4 (Common.fact 190).pointIds 190), Tip0014_0033, (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M7300_7500.SplitData.node0032 := by
  change Tree.branch (166 : Fin 172) _ = Tree.branch (166 : Fin 172) _
  apply congrArg (Tree.branch (166 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0031 : Block := .branch 133 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 180).pointIds 180), (.leaf 1 (Common.fact 181).pointIds 181), (.leaf 2 (Common.fact 182).pointIds 182), (.leaf 3 (Common.fact 183).pointIds 183), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), B0032]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M7300_7500.SplitData.node0031 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0032

def B0030 : Block := .branch 157 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B0031, (.leaf 5 (Common.fact 179).pointIds 179), (.leaf 0 [] 0)]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M7300_7500.SplitData.node0030 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0031
  · rfl
  · rfl

def B0029 : Block := .branch 125 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 169).pointIds 169), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B0030, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0029 : B0029.tree = HexagonCover.NBand.M7300_7500.SplitData.node0029 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0030
  · rfl

def B0028 : Block := .branch 164 ![288230376151712129, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 163).pointIds 163), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0029]
theorem treeEq0028 : B0028.tree = HexagonCover.NBand.M7300_7500.SplitData.node0028 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0029

def B0027 : Block := .branch 58 ![385, 72058693549557250, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![B0028, Tip0014_0073, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M7300_7500.SplitData.node0027 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0028
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0026 : Block := .branch 56 ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 153).pointIds 153), B0027, Tip0014_2318, (.leaf 3 (Common.fact 154).pointIds 154), (.leaf 4 (Common.fact 155).pointIds 155), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M7300_7500.SplitData.node0026 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0027
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 55 ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936] ![(.leaf 0 (Common.fact 81).pointIds 81), B0015, B0026, (.leaf 3 (Common.fact 82).pointIds 82), (.leaf 4 (Common.fact 83).pointIds 83), (.leaf 5 (Common.fact 84).pointIds 84), (.leaf 6 (Common.fact 85).pointIds 85)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M7300_7500.SplitData.node0014 := by
  change Tree.branch (55 : Fin 172) _ = Tree.branch (55 : Fin 172) _
  apply congrArg (Tree.branch (55 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0015
  · exact treeEq0026
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0014 : B0014.accepted = true := by decide +kernel
theorem checked0014 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0014 (maskNeeds ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891109096836968272374173007936]) := by
  rw [← treeEq0014]
  exact B0014.sound accepted0014
#print axioms checked0014

def B2939 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq2939 : B2939.tree = HexagonCover.NBand.M7300_7500.SplitData.node2939 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2938 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2939]
theorem treeEq2938 : B2938.tree = HexagonCover.NBand.M7300_7500.SplitData.node2938 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2939

def B2937 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2938, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2937 : B2937.tree = HexagonCover.NBand.M7300_7500.SplitData.node2937 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2938
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2936 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2937]
theorem treeEq2936 : B2936.tree = HexagonCover.NBand.M7300_7500.SplitData.node2936 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2937

def B2935 : Block := .branch 169 ![2535301200456458802993406411137, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2936, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2935 : B2935.tree = HexagonCover.NBand.M7300_7500.SplitData.node2935 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2936
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2934 : Block := .branch 170 ![2535301200456458802993406411137, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B2935, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2934 : B2934.tree = HexagonCover.NBand.M7300_7500.SplitData.node2934 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2935
  · rfl

def B2947 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq2947 : B2947.tree = HexagonCover.NBand.M7300_7500.SplitData.node2947 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2946 : Block := .branch 100 ![385, 1461501637330902918204303802735925709793382106626, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B2947, (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq2946 : B2946.tree = HexagonCover.NBand.M7300_7500.SplitData.node2946 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2947
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2945 : Block := .branch 160 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B2946, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq2945 : B2945.tree = HexagonCover.NBand.M7300_7500.SplitData.node2945 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2946
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2944 : Block := .branch 162 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B2945, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq2944 : B2944.tree = HexagonCover.NBand.M7300_7500.SplitData.node2944 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2945
  · rfl
  · rfl
  · rfl

def B2943 : Block := .branch 171 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2944]
theorem treeEq2943 : B2943.tree = HexagonCover.NBand.M7300_7500.SplitData.node2943 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2944

def B2942 : Block := .branch 170 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B2943, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2942 : B2942.tree = HexagonCover.NBand.M7300_7500.SplitData.node2942 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2943
  · rfl
  · rfl

def B2941 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B2942, (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2941 : B2941.tree = HexagonCover.NBand.M7300_7500.SplitData.node2941 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2942
  · rfl

def B2940 : Block := .branch 168 ![2535301200456458802993406411137, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![B2941, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq2940 : B2940.tree = HexagonCover.NBand.M7300_7500.SplitData.node2940 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2941
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2933 : Block := .branch 108 ![2535301200456458802993406411137, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B2934, (.leaf 5 (Common.fact 308).pointIds 308), B2940]
theorem treeEq2933 : B2933.tree = HexagonCover.NBand.M7300_7500.SplitData.node2933 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2934
  · rfl
  · exact treeEq2940

theorem accepted2933 : B2933.accepted = true := by decide +kernel
theorem checked2933 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2933 (maskNeeds ![2535301200456458802993406411137, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2933]
  exact B2933.sound accepted2933
#print axioms checked2933

def Tip2931_2933 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2933 ![2535301200456458802993406411137, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked2933
def B2955 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq2955 : B2955.tree = HexagonCover.NBand.M7300_7500.SplitData.node2955 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2954 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2955, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq2954 : B2954.tree = HexagonCover.NBand.M7300_7500.SplitData.node2954 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2955
  · rfl
  · rfl

def B2953 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2954]
theorem treeEq2953 : B2953.tree = HexagonCover.NBand.M7300_7500.SplitData.node2953 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2954

def B2952 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B2953, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2952 : B2952.tree = HexagonCover.NBand.M7300_7500.SplitData.node2952 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2953
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2951 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2952]
theorem treeEq2951 : B2951.tree = HexagonCover.NBand.M7300_7500.SplitData.node2951 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2952

def B2950 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B2951, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2950 : B2950.tree = HexagonCover.NBand.M7300_7500.SplitData.node2950 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2951
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2949 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2950, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2949 : B2949.tree = HexagonCover.NBand.M7300_7500.SplitData.node2949 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2950
  · rfl

def B2948 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2949, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq2948 : B2948.tree = HexagonCover.NBand.M7300_7500.SplitData.node2948 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2949
  · rfl
  · rfl

def B2932 : Block := .branch 101 ![2475880078570760549798248833, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip2931_2933, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B2948]
theorem treeEq2932 : B2932.tree = HexagonCover.NBand.M7300_7500.SplitData.node2932 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2948

def B2963 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq2963 : B2963.tree = HexagonCover.NBand.M7300_7500.SplitData.node2963 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2962 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2963, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq2962 : B2962.tree = HexagonCover.NBand.M7300_7500.SplitData.node2962 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2963
  · rfl
  · rfl

def B2961 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2962]
theorem treeEq2961 : B2961.tree = HexagonCover.NBand.M7300_7500.SplitData.node2961 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2962

def B2960 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B2961, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2960 : B2960.tree = HexagonCover.NBand.M7300_7500.SplitData.node2960 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2961
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2959 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2960]
theorem treeEq2959 : B2959.tree = HexagonCover.NBand.M7300_7500.SplitData.node2959 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2960

def B2958 : Block := .branch 169 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B2959, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2958 : B2958.tree = HexagonCover.NBand.M7300_7500.SplitData.node2958 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2959
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2957 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2958, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2957 : B2957.tree = HexagonCover.NBand.M7300_7500.SplitData.node2957 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2958
  · rfl

def B2956 : Block := .branch 171 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2957, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2956 : B2956.tree = HexagonCover.NBand.M7300_7500.SplitData.node2956 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2957
  · rfl
  · rfl

def B2931 : Block := .branch 91 ![385, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![B2932, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B2956]
theorem treeEq2931 : B2931.tree = HexagonCover.NBand.M7300_7500.SplitData.node2931 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2932
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2956

theorem accepted2931 : B2931.accepted = true := by decide +kernel
theorem checked2931 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2931 (maskNeeds ![385, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2931]
  exact B2931.sound accepted2931
#print axioms checked2931

def Tip2929_2931 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2931 ![385, 618970019859003657051702786, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked2931
def B2971 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq2971 : B2971.tree = HexagonCover.NBand.M7300_7500.SplitData.node2971 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2970 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2971, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq2970 : B2970.tree = HexagonCover.NBand.M7300_7500.SplitData.node2970 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2971
  · rfl
  · rfl

def B2969 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2970]
theorem treeEq2969 : B2969.tree = HexagonCover.NBand.M7300_7500.SplitData.node2969 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2970

def B2968 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B2969, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2968 : B2968.tree = HexagonCover.NBand.M7300_7500.SplitData.node2968 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2969
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2967 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2968]
theorem treeEq2967 : B2967.tree = HexagonCover.NBand.M7300_7500.SplitData.node2967 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2968

def B2966 : Block := .branch 169 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B2967, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2966 : B2966.tree = HexagonCover.NBand.M7300_7500.SplitData.node2966 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2967
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2965 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2966, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2965 : B2965.tree = HexagonCover.NBand.M7300_7500.SplitData.node2965 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2966
  · rfl

def B2964 : Block := .branch 171 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891882809361521635045984960576] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2965, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq2964 : B2964.tree = HexagonCover.NBand.M7300_7500.SplitData.node2964 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2965
  · rfl
  · rfl

def B2930 : Block := .branch 89 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip2929_2931, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B2964]
theorem treeEq2930 : B2930.tree = HexagonCover.NBand.M7300_7500.SplitData.node2930 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2964

def B2979 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq2979 : B2979.tree = HexagonCover.NBand.M7300_7500.SplitData.node2979 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2978 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2979, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq2978 : B2978.tree = HexagonCover.NBand.M7300_7500.SplitData.node2978 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2979
  · rfl
  · rfl

def B2977 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2978]
theorem treeEq2977 : B2977.tree = HexagonCover.NBand.M7300_7500.SplitData.node2977 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2978

def B2976 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516473233940747894922285678656] ![B2977, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2976 : B2976.tree = HexagonCover.NBand.M7300_7500.SplitData.node2976 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2977
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2975 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2976]
theorem treeEq2975 : B2975.tree = HexagonCover.NBand.M7300_7500.SplitData.node2975 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2976

def B2974 : Block := .branch 169 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B2975, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2974 : B2974.tree = HexagonCover.NBand.M7300_7500.SplitData.node2974 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2975
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2973 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2974, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2973 : B2973.tree = HexagonCover.NBand.M7300_7500.SplitData.node2973 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2974
  · rfl

def B2972 : Block := .branch 171 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2973, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq2972 : B2972.tree = HexagonCover.NBand.M7300_7500.SplitData.node2972 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2973
  · rfl
  · rfl

def B2929 : Block := .branch 86 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 939).pointIds 939), B2930, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B2972]
theorem treeEq2929 : B2929.tree = HexagonCover.NBand.M7300_7500.SplitData.node2929 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2930
  · rfl
  · rfl
  · exact treeEq2972

theorem accepted2929 : B2929.accepted = true := by decide +kernel
theorem checked2929 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2929 (maskNeeds ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2929]
  exact B2929.sound accepted2929
#print axioms checked2929

end HexagonCover.NBand.M7300_7500.SplitTree.Run0041
