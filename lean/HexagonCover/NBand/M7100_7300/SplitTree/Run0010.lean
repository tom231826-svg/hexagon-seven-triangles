import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0010
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0015_0027 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0027 ![385, 144257025075840514, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] HexagonCover.NBand.M7100_7300.SplitTree.Run0006.checked0027
def B0026 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 9408126880630106637835381146273527510433808, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 156).pointIds 156), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 158).pointIds 158)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M7100_7300.SplitData.node0026 := by
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

def B0025 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0026, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 151).pointIds 151)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M7100_7300.SplitData.node0025 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0026
  · rfl
  · rfl

def B0024 : Block := .branch 78 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0025]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M7100_7300.SplitData.node0024 := by
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
  · exact treeEq0025

def B0023 : Block := .branch 144 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0024, (.leaf 6 (Common.fact 139).pointIds 139)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M7100_7300.SplitData.node0023 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024
  · rfl

def B0022 : Block := .branch 87 ![385, 180145084606449154, 36893488147419109380, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257593281732674916694546186304] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0023]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M7100_7300.SplitData.node0022 := by
  change Tree.branch (87 : Fin 173) _ = Tree.branch (87 : Fin 173) _
  apply congrArg (Tree.branch (87 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023

def B0021 : Block := .branch 65 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3832940580997450852451451578111437133938704, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0022, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 127).pointIds 127)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M7100_7300.SplitData.node0021 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0022
  · rfl
  · rfl
  · rfl
  · rfl

def B0020 : Block := .branch 138 ![385, 180145084606449154, 6148, 38685626227668133590622216, 3484491437270409865864955980101306485407760, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0021, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 121).pointIds 121)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M7100_7300.SplitData.node0020 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl

def B0019 : Block := .branch 139 ![385, 180145084606449154, 6148, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0020, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 115).pointIds 115)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M7100_7300.SplitData.node0019 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl

def B0018 : Block := .branch 140 ![385, 180145084606449154, 6148, 38685626227668133590622216, 2787593149816327892691964784081045188345872, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0019, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 109).pointIds 109)]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M7100_7300.SplitData.node0018 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019
  · rfl
  · rfl

def B0017 : Block := .branch 141 ![385, 180145084606449154, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257902766742496261763270967360] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0018, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 103).pointIds 103)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M7100_7300.SplitData.node0017 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018
  · rfl
  · rfl

def B0016 : Block := .branch 89 ![385, 180145084606449154, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 92).pointIds 92), (.leaf 1 (Common.fact 93).pointIds 93), (.leaf 2 (Common.fact 94).pointIds 94), (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), B0017]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M7100_7300.SplitData.node0016 := by
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
  · exact treeEq0017

def B0015 : Block := .branch 55 ![385, 144257025075840514, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 87).pointIds 87), B0016, Tip0015_0027, (.leaf 3 (Common.fact 88).pointIds 88), (.leaf 4 (Common.fact 89).pointIds 89), (.leaf 5 (Common.fact 90).pointIds 90), (.leaf 6 (Common.fact 91).pointIds 91)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M7100_7300.SplitData.node0015 := by
  change Tree.branch (55 : Fin 173) _ = Tree.branch (55 : Fin 173) _
  apply congrArg (Tree.branch (55 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0015 : B0015.accepted = true := by decide +kernel
theorem checked0015 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0015 (maskNeeds ![385, 144257025075840514, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248]) := by
  rw [← treeEq0015]
  exact B0015.sound accepted0015
#print axioms checked0015

def B0826 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0826 : B0826.tree = HexagonCover.NBand.M7100_7300.SplitData.node0826 := by
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
  · rfl

def B0825 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0826]
theorem treeEq0825 : B0825.tree = HexagonCover.NBand.M7100_7300.SplitData.node0825 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0826

def B0824 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0825, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0824 : B0824.tree = HexagonCover.NBand.M7100_7300.SplitData.node0824 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0825
  · rfl
  · rfl

def B0823 : Block := .branch 160 ![385, 906694581024491483170306, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 906).pointIds 906), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0824]
theorem treeEq0823 : B0823.tree = HexagonCover.NBand.M7100_7300.SplitData.node0823 := by
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
  · exact treeEq0824

def B0822 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0823, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0822 : B0822.tree = HexagonCover.NBand.M7100_7300.SplitData.node0822 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0823
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0821 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0822, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0821 : B0821.tree = HexagonCover.NBand.M7100_7300.SplitData.node0821 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0822
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0820 : Block := .branch 168 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0821, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0820 : B0820.tree = HexagonCover.NBand.M7100_7300.SplitData.node0820 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0821
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0819 : Block := .branch 163 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0820]
theorem treeEq0819 : B0819.tree = HexagonCover.NBand.M7100_7300.SplitData.node0819 := by
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
  · exact treeEq0820

def B0818 : Block := .branch 165 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0819, (.leaf 0 [] 0)]
theorem treeEq0818 : B0818.tree = HexagonCover.NBand.M7100_7300.SplitData.node0818 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0819
  · rfl

def B0817 : Block := .branch 167 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0818, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M7100_7300.SplitData.node0817 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0818
  · rfl

def B0816 : Block := .branch 142 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0817, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M7100_7300.SplitData.node0816 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0817
  · rfl
  · rfl

def B0815 : Block := .branch 144 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0816, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M7100_7300.SplitData.node0815 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0816
  · rfl

def B0814 : Block := .branch 170 ![385, 302231671217176895817218, 18446745173221185540, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0815]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M7100_7300.SplitData.node0814 := by
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
  · exact treeEq0815

def B0830 : Block := .branch 161 ![385, 1538, 18446745173221185540, 1496577676626844588240573307387100039795808514629640, 98320, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), (.leaf 3 (Common.fact 667).pointIds 667), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0830 : B0830.tree = HexagonCover.NBand.M7100_7300.SplitData.node0830 := by
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

def B0829 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), B0830, (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0829 : B0829.tree = HexagonCover.NBand.M7100_7300.SplitData.node0829 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0830
  · rfl
  · rfl
  · rfl

def B0828 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0829]
theorem treeEq0828 : B0828.tree = HexagonCover.NBand.M7100_7300.SplitData.node0828 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0829

def B0827 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0828, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0827 : B0827.tree = HexagonCover.NBand.M7100_7300.SplitData.node0827 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0828
  · rfl
  · rfl

def B0813 : Block := .branch 86 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0814, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0827]
theorem treeEq0813 : B0813.tree = HexagonCover.NBand.M7100_7300.SplitData.node0813 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0814
  · rfl
  · rfl
  · exact treeEq0827

theorem accepted0813 : B0813.accepted = true := by decide +kernel
theorem checked0813 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0813 (maskNeeds ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0813]
  exact B0813.sound accepted0813
#print axioms checked0813

def B0869 : Block := .branch 79 ![374144419156732414710611177030381668558235328577921, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 911).pointIds 911), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0869 : B0869.tree = HexagonCover.NBand.M7100_7300.SplitData.node0869 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0868 : Block := .branch 159 ![374144419156732414710611177030381668558235328577921, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 714).pointIds 714), B0869, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0868 : B0868.tree = HexagonCover.NBand.M7100_7300.SplitData.node0868 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0869
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0867 : Block := .branch 124 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B0868, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0867 : B0867.tree = HexagonCover.NBand.M7100_7300.SplitData.node0867 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0868
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0866 : Block := .branch 128 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0867, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0866 : B0866.tree = HexagonCover.NBand.M7100_7300.SplitData.node0866 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0867
  · rfl
  · rfl
  · rfl

def B0865 : Block := .branch 138 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0866, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0865 : B0865.tree = HexagonCover.NBand.M7100_7300.SplitData.node0865 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0866
  · rfl
  · rfl

def B0864 : Block := .branch 139 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0865, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0864 : B0864.tree = HexagonCover.NBand.M7100_7300.SplitData.node0864 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0865
  · rfl
  · rfl

def B0863 : Block := .branch 140 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0864, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0863 : B0863.tree = HexagonCover.NBand.M7100_7300.SplitData.node0863 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0864
  · rfl
  · rfl

def B0862 : Block := .branch 141 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0863, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0862 : B0862.tree = HexagonCover.NBand.M7100_7300.SplitData.node0862 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0863
  · rfl
  · rfl

def B0861 : Block := .branch 142 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0862, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0861 : B0861.tree = HexagonCover.NBand.M7100_7300.SplitData.node0861 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0862
  · rfl
  · rfl

def B0860 : Block := .branch 165 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B0861, (.leaf 0 [] 0)]
theorem treeEq0860 : B0860.tree = HexagonCover.NBand.M7100_7300.SplitData.node0860 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0861
  · rfl

def B0859 : Block := .branch 167 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B0860, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0859 : B0859.tree = HexagonCover.NBand.M7100_7300.SplitData.node0859 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0860
  · rfl

def B0858 : Block := .branch 143 ![374144419156711147062678618376415207645270843064705, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B0859, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0858 : B0858.tree = HexagonCover.NBand.M7100_7300.SplitData.node0858 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0859
  · rfl
  · rfl

def B0857 : Block := .branch 170 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0858]
theorem treeEq0857 : B0857.tree = HexagonCover.NBand.M7100_7300.SplitData.node0857 := by
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
  · exact treeEq0858

def B0856 : Block := .branch 161 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B0857, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0856 : B0856.tree = HexagonCover.NBand.M7100_7300.SplitData.node0856 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0857
  · rfl
  · rfl
  · rfl

def B0855 : Block := .branch 75 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0856, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0855 : B0855.tree = HexagonCover.NBand.M7100_7300.SplitData.node0855 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0856
  · rfl
  · rfl
  · rfl
  · rfl

def B0854 : Block := .branch 162 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0855, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0854 : B0854.tree = HexagonCover.NBand.M7100_7300.SplitData.node0854 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0855
  · rfl
  · rfl
  · rfl

def B0853 : Block := .branch 172 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B0854]
theorem treeEq0853 : B0853.tree = HexagonCover.NBand.M7100_7300.SplitData.node0853 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0854

def B0852 : Block := .branch 151 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0853, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0852 : B0852.tree = HexagonCover.NBand.M7100_7300.SplitData.node0852 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0853
  · rfl
  · rfl

def B0851 : Block := .branch 132 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0852]
theorem treeEq0851 : B0851.tree = HexagonCover.NBand.M7100_7300.SplitData.node0851 := by
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
  · exact treeEq0852

def B0850 : Block := .branch 78 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B0851, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0850 : B0850.tree = HexagonCover.NBand.M7100_7300.SplitData.node0850 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0851
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0850 : B0850.accepted = true := by decide +kernel
theorem checked0850 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0850 (maskNeeds ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq0850]
  exact B0850.sound accepted0850
#print axioms checked0850

def Tip0841_0850 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0850 ![374144419156711147062678618376415207645270843064705, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked0850
def B0849 : Block := .branch 101 ![374144419156711147060143317175958748842277436653953, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip0841_0850, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0849 : B0849.tree = HexagonCover.NBand.M7100_7300.SplitData.node0849 := by
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
  · rfl

def B0848 : Block := .branch 168 ![590295810358705652097, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![B0849, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0848 : B0848.tree = HexagonCover.NBand.M7100_7300.SplitData.node0848 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0849
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0847 : Block := .branch 133 ![590295810358705652097, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0848]
theorem treeEq0847 : B0847.tree = HexagonCover.NBand.M7100_7300.SplitData.node0847 := by
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
  · exact treeEq0848

def B0846 : Block := .branch 157 ![590295810358705652097, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0847, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0846 : B0846.tree = HexagonCover.NBand.M7100_7300.SplitData.node0846 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0847
  · rfl
  · rfl

def B0845 : Block := .branch 169 ![10384593717070245552871351364092289, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B0846, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M7100_7300.SplitData.node0845 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0846
  · rfl

def B0878 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0878 : B0878.tree = HexagonCover.NBand.M7100_7300.SplitData.node0878 := by
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

def B0877 : Block := .branch 159 ![10384593717069655257060992658440577, 737941961279908349442, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B0878, (.leaf 1 (Common.fact 913).pointIds 913), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0877 : B0877.tree = HexagonCover.NBand.M7100_7300.SplitData.node0877 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0876 : Block := .branch 75 ![10384593717069655257060992658440577, 737941961279908349442, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0877, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq0876 : B0876.tree = HexagonCover.NBand.M7100_7300.SplitData.node0876 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0877
  · rfl
  · rfl
  · rfl
  · rfl

def B0875 : Block := .branch 170 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0876]
theorem treeEq0875 : B0875.tree = HexagonCover.NBand.M7100_7300.SplitData.node0875 := by
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
  · exact treeEq0876

def B0874 : Block := .branch 161 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 907).pointIds 907), B0875, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0874 : B0874.tree = HexagonCover.NBand.M7100_7300.SplitData.node0874 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0875
  · rfl
  · rfl
  · rfl

def B0873 : Block := .branch 168 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![B0874, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0873 : B0873.tree = HexagonCover.NBand.M7100_7300.SplitData.node0873 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0874
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0872 : Block := .branch 172 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0873]
theorem treeEq0872 : B0872.tree = HexagonCover.NBand.M7100_7300.SplitData.node0872 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0873

def B0871 : Block := .branch 171 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0872, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0871 : B0871.tree = HexagonCover.NBand.M7100_7300.SplitData.node0871 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0872
  · rfl
  · rfl

def B0870 : Block := .branch 160 ![10384593717069655257060992658440577, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 912).pointIds 912), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0871]
theorem treeEq0870 : B0870.tree = HexagonCover.NBand.M7100_7300.SplitData.node0870 := by
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
  · exact treeEq0871

def B0844 : Block := .branch 69 ![10384593717069655257060992658440577, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0845, B0870, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M7100_7300.SplitData.node0844 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0845
  · exact treeEq0870
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0880 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0880 : B0880.tree = HexagonCover.NBand.M7100_7300.SplitData.node0880 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0879 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B0880, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0879 : B0879.tree = HexagonCover.NBand.M7100_7300.SplitData.node0879 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0880
  · rfl
  · rfl

def B0843 : Block := .branch 68 ![10384593717069655257060992658440577, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B0844, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B0879]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M7100_7300.SplitData.node0843 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0844
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0879

def B0842 : Block := .branch 91 ![10384593717069655257060992658440577, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0843, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M7100_7300.SplitData.node0842 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0843
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0841 : Block := .branch 113 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0842, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M7100_7300.SplitData.node0841 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0842
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0841 : B0841.accepted = true := by decide +kernel
theorem checked0841 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0841 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0841]
  exact B0841.sound accepted0841
#print axioms checked0841

end HexagonCover.NBand.M7100_7300.SplitTree.Run0010
