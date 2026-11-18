import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0013
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0026 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 9408126880630106637835381146273527510433808, 393248, 21783388395240269019941013030989874069568] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 158).pointIds 158), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 160).pointIds 160)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M7500_7700.SplitData.node0026 := by
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

def B0025 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388395240269019941013030989874069568] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0026, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 153).pointIds 153)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M7500_7700.SplitData.node0025 := by
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

def B0024 : Block := .branch 78 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388395240268717709558127332580393024] ![(.leaf 0 (Common.fact 142).pointIds 142), (.leaf 1 (Common.fact 143).pointIds 143), (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0025]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M7500_7700.SplitData.node0024 := by
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

def B0023 : Block := .branch 98 ![385, 180143985094821378, 6148, 79286190953605839793929871368, 3832940580997450852451451578111437133938704, 393248, 21783388394923356067652500776958404591680] ![(.leaf 0 (Common.fact 136).pointIds 136), (.leaf 1 (Common.fact 137).pointIds 137), (.leaf 2 (Common.fact 138).pointIds 138), (.leaf 3 (Common.fact 139).pointIds 139), (.leaf 4 (Common.fact 140).pointIds 140), (.leaf 5 (Common.fact 141).pointIds 141), B0024]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M7500_7700.SplitData.node0023 := by
  change Tree.branch (98 : Fin 173) _ = Tree.branch (98 : Fin 173) _
  apply congrArg (Tree.branch (98 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0024

def B0022 : Block := .branch 85 ![385, 180143985094821378, 36893488147419109380, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388394923356067652500776958404591680] ![(.leaf 0 (Common.fact 130).pointIds 130), (.leaf 1 (Common.fact 131).pointIds 131), (.leaf 2 (Common.fact 132).pointIds 132), B0023, (.leaf 4 (Common.fact 133).pointIds 133), (.leaf 5 (Common.fact 134).pointIds 134), (.leaf 6 (Common.fact 135).pointIds 135)]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M7500_7700.SplitData.node0022 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0023
  · rfl
  · rfl
  · rfl

def B0021 : Block := .branch 144 ![385, 180143985094821378, 36893488147419109380, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388394923975037672143467095854153792] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0022, (.leaf 6 (Common.fact 129).pointIds 129)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M7500_7700.SplitData.node0021 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0022
  · rfl

def B0020 : Block := .branch 87 ![385, 180143985094821378, 36893488147419109380, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388394923820295167232794561491763264] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B0021]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M7500_7700.SplitData.node0020 := by
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
  · exact treeEq0021

def B0019 : Block := .branch 65 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21783388394923820295167232794561491763264] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0020, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 117).pointIds 117)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M7500_7700.SplitData.node0019 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl
  · rfl
  · rfl

def B0018 : Block := .branch 122 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 3832940580997450852451451578111437133938704, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B0019]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M7500_7700.SplitData.node0018 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019

def B0017 : Block := .branch 138 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 3484491437270409865864955980101306485407760, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0018, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 105).pointIds 105)]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M7500_7700.SplitData.node0017 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018
  · rfl
  · rfl

def B0016 : Block := .branch 139 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 2787593149816327892691964784081045188345872, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), B0017, (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 99).pointIds 99)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M7500_7700.SplitData.node0016 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0017
  · rfl
  · rfl

def B0015 : Block := .branch 140 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 2787593149816327892691964784081045188345872, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0016, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M7500_7700.SplitData.node0015 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0016
  · rfl
  · rfl

def B0014 : Block := .branch 141 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 98320, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B0015, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 87).pointIds 87)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M7500_7700.SplitData.node0014 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0015
  · rfl
  · rfl

def B0013 : Block := .branch 149 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 98320, 393248, 21778071482940680631675617566320370384960] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0014, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 81).pointIds 81)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M7500_7700.SplitData.node0013 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0014
  · rfl
  · rfl

def B0012 : Block := .branch 89 ![385, 180143985094821378, 6148, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), B0013]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M7500_7700.SplitData.node0012 := by
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
  · exact treeEq0013

theorem accepted0012 : B0012.accepted = true := by decide +kernel
theorem checked0012 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0012 (maskNeeds ![385, 180143985094821378, 6148, 79247505327378171660339273736, 98320, 393248, 21778071482940061661655974876182920822848]) := by
  rw [← treeEq0012]
  exact B0012.sound accepted0012
#print axioms checked0012

def B1065 : Block := .branch 124 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 98320, 393248, 11869048958202650982480078096588602233847872] ![(.leaf 0 (Common.fact 465).pointIds 465), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1065 : B1065.tree = HexagonCover.NBand.M7500_7700.SplitData.node1065 := by
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

def B1064 : Block := .branch 143 ![748288838313422294120286634955199815871152049357185, 1538, 6148, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), (.leaf 4 (Common.fact 893).pointIds 893), (.leaf 5 (Common.fact 569).pointIds 569), B1065]
theorem treeEq1064 : B1064.tree = HexagonCover.NBand.M7500_7700.SplitData.node1064 := by
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
  · exact treeEq1065

def B1063 : Block := .branch 86 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 891).pointIds 891), B1064, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 892).pointIds 892)]
theorem treeEq1063 : B1063.tree = HexagonCover.NBand.M7500_7700.SplitData.node1063 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1064
  · rfl
  · rfl
  · rfl

def B1062 : Block := .branch 89 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![(.leaf 0 (Common.fact 70).pointIds 70), B1063, (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq1062 : B1062.tree = HexagonCover.NBand.M7500_7700.SplitData.node1062 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1063
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1061 : Block := .branch 100 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1062, (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq1061 : B1061.tree = HexagonCover.NBand.M7500_7700.SplitData.node1061 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1062
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1060 : Block := .branch 112 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1061, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), (.leaf 6 (Common.fact 888).pointIds 888)]
theorem treeEq1060 : B1060.tree = HexagonCover.NBand.M7500_7700.SplitData.node1060 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1061
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1059 : Block := .branch 113 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1060, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 887).pointIds 887)]
theorem treeEq1059 : B1059.tree = HexagonCover.NBand.M7500_7700.SplitData.node1059 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1060
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1058 : Block := .branch 128 ![748288838313422294120286634955199815871152049357185, 1538, 18446884811197913092, 24584, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B1059, (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 886).pointIds 886)]
theorem treeEq1058 : B1058.tree = HexagonCover.NBand.M7500_7700.SplitData.node1058 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1059
  · rfl
  · rfl
  · rfl

def B1057 : Block := .branch 90 ![748288838313422294120286634955199815871152049357185, 1461501637330902918203685134947737923313226221058, 18446884811197913092, 24584, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707226054711899632486518114208775121176887360] ![B1058, (.leaf 1 (Common.fact 750).pointIds 750), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 885).pointIds 885)]
theorem treeEq1057 : B1057.tree = HexagonCover.NBand.M7500_7700.SplitData.node1057 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1058
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1056 : Block := .branch 168 ![748288838313422294120286634955199815871152049357185, 1461501637330902918203685134947737923313226221058, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![B1057, (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 884).pointIds 884), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq1056 : B1056.tree = HexagonCover.NBand.M7500_7700.SplitData.node1056 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1057
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1055 : Block := .branch 160 ![748288838313422294120286634955199815871152049357185, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![(.leaf 0 (Common.fact 362).pointIds 362), B1056, (.leaf 2 (Common.fact 883).pointIds 883), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq1055 : B1055.tree = HexagonCover.NBand.M7500_7700.SplitData.node1055 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1056
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1054 : Block := .branch 75 ![748288838313422294120286634955199815871152049357185, 302231454903657293678082, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B1055, (.leaf 3 (Common.fact 881).pointIds 881), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq1054 : B1054.tree = HexagonCover.NBand.M7500_7700.SplitData.node1054 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1055
  · rfl
  · rfl
  · rfl
  · rfl

def B1053 : Block := .branch 162 ![748288838313422294120286634955199815871152049357185, 302231454903657293678082, 18446884811197913092, 38685626227668133590622216, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310707231499229770367501933528202494029468270656] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B1054, (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq1053 : B1053.tree = HexagonCover.NBand.M7500_7700.SplitData.node1053 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1054
  · rfl
  · rfl
  · rfl

def B1052 : Block := .branch 139 ![748288838313422294120286634955199815871152049357185, 302231454903657293678082, 18446884811197913092, 79266848140492005727134572552, 2993341609077587304245624643721960783370647796547600, 42535295865117307932921825928971419680, 5986310706534600942316285528760537006473768171208768] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B1053]
theorem treeEq1052 : B1052.tree = HexagonCover.NBand.M7500_7700.SplitData.node1052 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1053

def B1051 : Block := .branch 151 ![748288838313422294120286634955199815871152049357185, 302231454903657293678082, 18446884811197913092, 79266848140492005727134572552, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 5986310706534600942316285528760537006473768171208768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B1052, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq1051 : B1051.tree = HexagonCover.NBand.M7500_7700.SplitData.node1051 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1052
  · rfl
  · rfl

def B1050 : Block := .branch 172 ![748288838313422294120286634955199815871152049357185, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), (.leaf 4 (Common.fact 878).pointIds 878), (.leaf 5 (Common.fact 879).pointIds 879), B1051]
theorem treeEq1050 : B1050.tree = HexagonCover.NBand.M7500_7700.SplitData.node1050 := by
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
  · exact treeEq1051

def B1049 : Block := .branch 171 ![748288838313422294120286634955199815871152049357185, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), B1050, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1049 : B1049.tree = HexagonCover.NBand.M7500_7700.SplitData.node1049 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1050
  · rfl
  · rfl

def B1048 : Block := .branch 170 ![748288838313422294120286634955199815871152049357185, 302231599018845369533954, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B1049, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq1048 : B1048.tree = HexagonCover.NBand.M7500_7700.SplitData.node1048 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1049
  · rfl

def B1047 : Block := .branch 79 ![748288838313422294120286634350736906063837462004097, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B1048, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq1047 : B1047.tree = HexagonCover.NBand.M7500_7700.SplitData.node1047 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1048
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1046 : Block := .branch 169 ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B1047, (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq1046 : B1046.tree = HexagonCover.NBand.M7500_7700.SplitData.node1046 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1047
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted1046 : B1046.accepted = true := by decide +kernel
theorem checked1046 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1046 (maskNeeds ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072]) := by
  rw [← treeEq1046]
  exact B1046.sound accepted1046
#print axioms checked1046

def B1084 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq1084 : B1084.tree = HexagonCover.NBand.M7500_7700.SplitData.node1084 := by
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

def B1083 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1084]
theorem treeEq1083 : B1083.tree = HexagonCover.NBand.M7500_7700.SplitData.node1083 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1084

def B1082 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B1083, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M7500_7700.SplitData.node1082 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1083
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1081 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1082, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M7500_7700.SplitData.node1081 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1082
  · rfl

def B1080 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1081, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M7500_7700.SplitData.node1080 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1081
  · rfl
  · rfl

def B1079 : Block := .branch 88 ![10384593717070245552871351364092289, 302231671076439407461890, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1080]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M7500_7700.SplitData.node1079 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1080

def B1090 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M7500_7700.SplitData.node1090 := by
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

def B1089 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 2923003296439877319664344883839962976840842739776] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1090, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M7500_7700.SplitData.node1089 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1090
  · rfl
  · rfl

def B1088 : Block := .branch 79 ![1496577676626844598625166985771719364999026288099713, 216172782113785346, 6148, 24584, 98320, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 901).pointIds 901), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1089]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M7500_7700.SplitData.node1088 := by
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
  · exact treeEq1089

def B1087 : Block := .branch 170 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B1088, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq1087 : B1087.tree = HexagonCover.NBand.M7500_7700.SplitData.node1087 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1088
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1086 : Block := .branch 171 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1087, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1086 : B1086.tree = HexagonCover.NBand.M7500_7700.SplitData.node1086 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1087
  · rfl

def B1085 : Block := .branch 172 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1086, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq1085 : B1085.tree = HexagonCover.NBand.M7500_7700.SplitData.node1085 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1086
  · rfl
  · rfl

def B1078 : Block := .branch 78 ![10384593717070245552871351364092289, 216172782113785346, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B1079, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1085]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M7500_7700.SplitData.node1078 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1079
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1085

def B1095 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq1095 : B1095.tree = HexagonCover.NBand.M7500_7700.SplitData.node1095 := by
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

def B1094 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B1095]
theorem treeEq1094 : B1094.tree = HexagonCover.NBand.M7500_7700.SplitData.node1094 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1095

def B1093 : Block := .branch 170 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B1094, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq1093 : B1093.tree = HexagonCover.NBand.M7500_7700.SplitData.node1093 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1094
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1092 : Block := .branch 171 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B1093, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1092 : B1092.tree = HexagonCover.NBand.M7500_7700.SplitData.node1092 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1093
  · rfl

def B1091 : Block := .branch 142 ![10384593717070245552871351364092289, 144115188075857410, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1092, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq1091 : B1091.tree = HexagonCover.NBand.M7500_7700.SplitData.node1091 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1092
  · rfl
  · rfl

def B1077 : Block := .branch 76 ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 900).pointIds 900), B1078, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B1091]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M7500_7700.SplitData.node1077 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1078
  · rfl
  · rfl
  · rfl
  · exact treeEq1091

theorem accepted1077 : B1077.accepted = true := by decide +kernel
theorem checked1077 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1077 (maskNeeds ![10384593717070245552871351364092289, 442938030551143024130, 18446884811197913092, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq1077]
  exact B1077.sound accepted1077
#print axioms checked1077

def Tip1039_1046 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node1046 ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] checked1046
def B1045 : Block := .branch 132 ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), Tip1039_1046]
theorem treeEq1045 : B1045.tree = HexagonCover.NBand.M7500_7700.SplitData.node1045 := by
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

def B1044 : Block := .branch 133 ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B1045]
theorem treeEq1044 : B1044.tree = HexagonCover.NBand.M7500_7700.SplitData.node1044 := by
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
  · exact treeEq1045

def B1043 : Block := .branch 157 ![385, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1044, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq1043 : B1043.tree = HexagonCover.NBand.M7500_7700.SplitData.node1043 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1044
  · rfl
  · rfl

def B1042 : Block := .branch 125 ![590295810358705652097, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B1043, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq1042 : B1042.tree = HexagonCover.NBand.M7500_7700.SplitData.node1042 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1043
  · rfl

def B1041 : Block := .branch 149 ![590295810358705652097, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1042, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq1041 : B1041.tree = HexagonCover.NBand.M7500_7700.SplitData.node1041 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1042
  · rfl
  · rfl

def B1040 : Block := .branch 88 ![590295810358705652097, 302231671076439407461890, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B1041]
theorem treeEq1040 : B1040.tree = HexagonCover.NBand.M7500_7700.SplitData.node1040 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1041

def B1071 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 898).pointIds 898)]
theorem treeEq1071 : B1071.tree = HexagonCover.NBand.M7500_7700.SplitData.node1071 := by
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

def B1070 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129960912307610063340044352] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1071, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 897).pointIds 897)]
theorem treeEq1070 : B1070.tree = HexagonCover.NBand.M7500_7700.SplitData.node1070 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1071
  · rfl
  · rfl

def B1069 : Block := .branch 79 ![1496577676626844588240573268702064107938033629659521, 216172782113785346, 6148, 24584, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 896).pointIds 896), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), B1070]
theorem treeEq1069 : B1069.tree = HexagonCover.NBand.M7500_7700.SplitData.node1069 := by
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
  · exact treeEq1070

def B1068 : Block := .branch 170 ![590295810358705652097, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 2993155353253689176481146537402947624255349848408096, 21778071483257129356449397802748752691264] ![B1069, (.leaf 1 (Common.fact 871).pointIds 871), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 895).pointIds 895)]
theorem treeEq1068 : B1068.tree = HexagonCover.NBand.M7500_7700.SplitData.node1068 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1069
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1067 : Block := .branch 171 ![590295810358705652097, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 873).pointIds 873), (.leaf 2 (Common.fact 874).pointIds 874), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B1068, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1067 : B1067.tree = HexagonCover.NBand.M7500_7700.SplitData.node1067 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1068
  · rfl

def B1066 : Block := .branch 172 ![590295810358705652097, 216172782113785346, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 875).pointIds 875), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 877).pointIds 877), (.leaf 3 (Common.fact 816).pointIds 816), B1067, (.leaf 5 (Common.fact 879).pointIds 879), (.leaf 6 (Common.fact 894).pointIds 894)]
theorem treeEq1066 : B1066.tree = HexagonCover.NBand.M7500_7700.SplitData.node1066 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1067
  · rfl
  · rfl

def B1039 : Block := .branch 78 ![590295810358705652097, 216172782113785346, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B1040, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B1066]
theorem treeEq1039 : B1039.tree = HexagonCover.NBand.M7500_7700.SplitData.node1039 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1040
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1066

theorem accepted1039 : B1039.accepted = true := by decide +kernel
theorem checked1039 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node1039 (maskNeeds ![590295810358705652097, 216172782113785346, 18446884811197913092, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq1039]
  exact B1039.sound accepted1039
#print axioms checked1039

end HexagonCover.NBand.M7500_7700.SplitTree.Run0013
