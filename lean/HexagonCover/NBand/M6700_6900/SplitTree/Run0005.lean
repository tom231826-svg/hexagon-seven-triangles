import HexagonCover.NBand.M6700_6900.SplitData
import HexagonCover.NBand.M6700_6900.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6700_6900.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M6700_6900

abbrev Block := Chunk (n := 175) (Certificate := Fin 929) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0407 : Block := .branch 112 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 25815964921834847218632828946762079234078575359950912] ![(.leaf 0 (Common.fact 903).pointIds 903), (.leaf 1 (Common.fact 210).pointIds 210), (.leaf 2 (Common.fact 211).pointIds 211), (.leaf 3 (Common.fact 212).pointIds 212), (.leaf 4 (Common.fact 213).pointIds 213), (.leaf 5 (Common.fact 214).pointIds 214), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M6700_6900.SplitData.node0407 := by
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

def B0406 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 11150372599265311570767859136324180753383456, 25815964921834847218632828946762079234078575359950912] ![B0407, (.leaf 1 (Common.fact 927).pointIds 927), (.leaf 2 (Common.fact 928).pointIds 928), (.leaf 3 (Common.fact 789).pointIds 789), (.leaf 4 (Common.fact 670).pointIds 670), (.leaf 5 (Common.fact 790).pointIds 790), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M6700_6900.SplitData.node0406 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0407
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0405 : Block := .branch 174 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 14965777479892292235385673216157722846024317431545872, 11150372599265311570767859136324180753383456, 1870722095805333806783656647538498240035776575832128] ![(.leaf 0 (Common.fact 898).pointIds 898), (.leaf 1 (Common.fact 925).pointIds 925), (.leaf 2 (Common.fact 926).pointIds 926), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 817).pointIds 817), (.leaf 5 (Common.fact 794).pointIds 794), B0406]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M6700_6900.SplitData.node0405 := by
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
  · exact treeEq0406

def B0404 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783973714931060208058685114024000] ![(.leaf 0 (Common.fact 895).pointIds 895), (.leaf 1 (Common.fact 923).pointIds 923), (.leaf 2 (Common.fact 924).pointIds 924), (.leaf 3 (Common.fact 798).pointIds 798), B0405, (.leaf 5 (Common.fact 658).pointIds 658), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M6700_6900.SplitData.node0404 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0405
  · rfl
  · rfl

def B0403 : Block := .branch 59 ![42535295865118516858741440558145732993, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 894).pointIds 894), B0404, (.leaf 2 (Common.fact 453).pointIds 453), (.leaf 3 (Common.fact 454).pointIds 454), (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M6700_6900.SplitData.node0403 := by
  change Tree.branch (59 : Fin 175) _ = Tree.branch (59 : Fin 175) _
  apply congrArg (Tree.branch (59 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0404
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0402 : Block := .branch 166 ![42535295865118516858741440558145732993, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1894106122002628253475232981739530557718248759492672] ![B0403, (.leaf 1 (Common.fact 216).pointIds 216), (.leaf 2 (Common.fact 217).pointIds 217), (.leaf 3 (Common.fact 218).pointIds 218), (.leaf 4 (Common.fact 219).pointIds 219), (.leaf 5 (Common.fact 810).pointIds 810), (.leaf 6 (Common.fact 811).pointIds 811)]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M6700_6900.SplitData.node0402 := by
  change Tree.branch (166 : Fin 175) _ = Tree.branch (166 : Fin 175) _
  apply congrArg (Tree.branch (166 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0403
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0401 : Block := .branch 164 ![42535295865118516858741440558145732993, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 876).pointIds 876), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B0402]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M6700_6900.SplitData.node0401 := by
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
  · exact treeEq0402

def B0400 : Block := .branch 125 ![1208925819614629174706561, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 11150372599265311570767859136324180753383456, 1870722095805333806783974024416070029403753838805056] ![B0401, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 808).pointIds 808), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M6700_6900.SplitData.node0400 := by
  change Tree.branch (125 : Fin 175) _ = Tree.branch (125 : Fin 175) _
  apply congrArg (Tree.branch (125 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0401
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0399 : Block := .branch 143 ![1208925819614629174706561, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 11972622126638603058904526678754775221768967583531024, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 601).pointIds 601), (.leaf 1 (Common.fact 602).pointIds 602), (.leaf 2 (Common.fact 603).pointIds 603), (.leaf 3 (Common.fact 604).pointIds 604), (.leaf 4 (Common.fact 785).pointIds 785), B0400, (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M6700_6900.SplitData.node0399 := by
  change Tree.branch (143 : Fin 175) _ = Tree.branch (143 : Fin 175) _
  apply congrArg (Tree.branch (143 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0400
  · rfl

def B0398 : Block := .branch 173 ![1208925819614629174706561, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1870722095805333806783974024416070029403753838805056] ![(.leaf 0 (Common.fact 891).pointIds 891), (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 782).pointIds 782), B0399, (.leaf 5 (Common.fact 783).pointIds 783), (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M6700_6900.SplitData.node0398 := by
  change Tree.branch (173 : Fin 175) _ = Tree.branch (173 : Fin 175) _
  apply congrArg (Tree.branch (173 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0399
  · rfl
  · rfl

def B0397 : Block := .branch 170 ![1208925819614629174706561, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 888).pointIds 888), (.leaf 1 (Common.fact 919).pointIds 919), (.leaf 2 (Common.fact 920).pointIds 920), (.leaf 3 (Common.fact 766).pointIds 766), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0398]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M6700_6900.SplitData.node0397 := by
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
  · exact treeEq0398

def B0396 : Block := .branch 80 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0397, (.leaf 1 (Common.fact 447).pointIds 447), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M6700_6900.SplitData.node0396 := by
  change Tree.branch (80 : Fin 175) _ = Tree.branch (80 : Fin 175) _
  apply congrArg (Tree.branch (80 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0397
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0395 : Block := .branch 92 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B0396, (.leaf 1 (Common.fact 441).pointIds 441), (.leaf 2 (Common.fact 442).pointIds 442), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 444).pointIds 444), (.leaf 5 (Common.fact 445).pointIds 445), (.leaf 6 (Common.fact 446).pointIds 446)]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M6700_6900.SplitData.node0395 := by
  change Tree.branch (92 : Fin 175) _ = Tree.branch (92 : Fin 175) _
  apply congrArg (Tree.branch (92 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0396
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0394 : Block := .branch 168 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 435).pointIds 435), (.leaf 1 (Common.fact 917).pointIds 917), (.leaf 2 (Common.fact 918).pointIds 918), (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), B0395]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M6700_6900.SplitData.node0394 := by
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
  · exact treeEq0395

theorem accepted0394 : B0394.accepted = true := by decide +kernel
theorem checked0394 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0394 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0394]
  exact B0394.sound accepted0394
#print axioms checked0394

def Tip0008_0028 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0028 ![385, 144257025075840514, 18482772870728521732, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6700_6900.SplitTree.Run0004.checked0028
def Tip0008_0380 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0380 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M6700_6900.SplitTree.Run0004.checked0380
def Tip0008_0394 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0394 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0394
def B0027 : Block := .branch 119 ![385, 1538, 6148, 79228162514264337593543974920, 5444517870735015415413993718908291481616, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), (.leaf 4 (Common.fact 162).pointIds 162), (.leaf 5 (Common.fact 163).pointIds 163), (.leaf 6 (Common.fact 164).pointIds 164)]
theorem treeEq0027 : B0027.tree = HexagonCover.NBand.M6700_6900.SplitData.node0027 := by
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

def B0026 : Block := .branch 132 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B0027, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 157).pointIds 157)]
theorem treeEq0026 : B0026.tree = HexagonCover.NBand.M6700_6900.SplitData.node0026 := by
  change Tree.branch (132 : Fin 175) _ = Tree.branch (132 : Fin 175) _
  apply congrArg (Tree.branch (132 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0027
  · rfl
  · rfl

def B0025 : Block := .branch 135 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), B0026, (.leaf 6 (Common.fact 151).pointIds 151)]
theorem treeEq0025 : B0025.tree = HexagonCover.NBand.M6700_6900.SplitData.node0025 := by
  change Tree.branch (135 : Fin 175) _ = Tree.branch (135 : Fin 175) _
  apply congrArg (Tree.branch (135 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0026
  · rfl

def B0024 : Block := .branch 78 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0025]
theorem treeEq0024 : B0024.tree = HexagonCover.NBand.M6700_6900.SplitData.node0024 := by
  change Tree.branch (78 : Fin 175) _ = Tree.branch (78 : Fin 175) _
  apply congrArg (Tree.branch (78 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0025

def B0023 : Block := .branch 65 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), B0024, (.leaf 3 (Common.fact 136).pointIds 136), (.leaf 4 (Common.fact 137).pointIds 137), (.leaf 5 (Common.fact 138).pointIds 138), (.leaf 6 (Common.fact 139).pointIds 139)]
theorem treeEq0023 : B0023.tree = HexagonCover.NBand.M6700_6900.SplitData.node0023 := by
  change Tree.branch (65 : Fin 175) _ = Tree.branch (65 : Fin 175) _
  apply congrArg (Tree.branch (65 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0024
  · rfl
  · rfl
  · rfl
  · rfl

def B0022 : Block := .branch 138 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), B0023, (.leaf 5 (Common.fact 132).pointIds 132), (.leaf 6 (Common.fact 133).pointIds 133)]
theorem treeEq0022 : B0022.tree = HexagonCover.NBand.M6700_6900.SplitData.node0022 := by
  change Tree.branch (138 : Fin 175) _ = Tree.branch (138 : Fin 175) _
  apply congrArg (Tree.branch (138 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0023
  · rfl
  · rfl

def B0021 : Block := .branch 139 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 124).pointIds 124), (.leaf 3 (Common.fact 125).pointIds 125), B0022, (.leaf 5 (Common.fact 126).pointIds 126), (.leaf 6 (Common.fact 127).pointIds 127)]
theorem treeEq0021 : B0021.tree = HexagonCover.NBand.M6700_6900.SplitData.node0021 := by
  change Tree.branch (139 : Fin 175) _ = Tree.branch (139 : Fin 175) _
  apply congrArg (Tree.branch (139 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0022
  · rfl
  · rfl

def B0020 : Block := .branch 140 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0021, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 121).pointIds 121)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M6700_6900.SplitData.node0020 := by
  change Tree.branch (140 : Fin 175) _ = Tree.branch (140 : Fin 175) _
  apply congrArg (Tree.branch (140 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0021
  · rfl
  · rfl

def B0019 : Block := .branch 141 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0020, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 115).pointIds 115)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M6700_6900.SplitData.node0019 := by
  change Tree.branch (141 : Fin 175) _ = Tree.branch (141 : Fin 175) _
  apply congrArg (Tree.branch (141 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl

def B0018 : Block := .branch 144 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257748024237585589228908576832] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), B0019, (.leaf 6 (Common.fact 109).pointIds 109)]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M6700_6900.SplitData.node0018 := by
  change Tree.branch (144 : Fin 175) _ = Tree.branch (144 : Fin 175) _
  apply congrArg (Tree.branch (144 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019
  · rfl

def B0017 : Block := .branch 89 ![385, 180145084606449154, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), (.leaf 4 (Common.fact 102).pointIds 102), (.leaf 5 (Common.fact 103).pointIds 103), B0018]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M6700_6900.SplitData.node0017 := by
  change Tree.branch (89 : Fin 175) _ = Tree.branch (89 : Fin 175) _
  apply congrArg (Tree.branch (89 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0018

def B0016 : Block := .branch 55 ![385, 144257025075840514, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 93).pointIds 93), B0017, Tip0008_0028, (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), (.leaf 6 (Common.fact 97).pointIds 97)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M6700_6900.SplitData.node0016 := by
  change Tree.branch (55 : Fin 175) _ = Tree.branch (55 : Fin 175) _
  apply congrArg (Tree.branch (55 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0017
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0015 : Block := .branch 47 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 88).pointIds 88), B0016, Tip0008_0380, (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), (.leaf 6 (Common.fact 92).pointIds 92)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M6700_6900.SplitData.node0015 := by
  change Tree.branch (47 : Fin 175) _ = Tree.branch (47 : Fin 175) _
  apply congrArg (Tree.branch (47 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 40 ![385, 144115188075857410, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 84).pointIds 84), B0015, Tip0008_0394, (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), (.leaf 5 (Common.fact 87).pointIds 87), (.leaf 0 [] 0)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M6700_6900.SplitData.node0014 := by
  change Tree.branch (40 : Fin 175) _ = Tree.branch (40 : Fin 175) _
  apply congrArg (Tree.branch (40 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0013 : Block := .branch 57 ![385, 1538, 18446744073709557764, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 78).pointIds 78), B0014, (.leaf 2 (Common.fact 79).pointIds 79), (.leaf 3 (Common.fact 80).pointIds 80), (.leaf 4 (Common.fact 81).pointIds 81), (.leaf 5 (Common.fact 82).pointIds 82), (.leaf 6 (Common.fact 83).pointIds 83)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M6700_6900.SplitData.node0013 := by
  change Tree.branch (57 : Fin 175) _ = Tree.branch (57 : Fin 175) _
  apply congrArg (Tree.branch (57 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0014
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 64 ![385, 1538, 6148, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 72).pointIds 72), (.leaf 1 (Common.fact 73).pointIds 73), B0013, (.leaf 3 (Common.fact 74).pointIds 74), (.leaf 4 (Common.fact 75).pointIds 75), (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M6700_6900.SplitData.node0012 := by
  change Tree.branch (64 : Fin 175) _ = Tree.branch (64 : Fin 175) _
  apply congrArg (Tree.branch (64 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0013
  · rfl
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 85 ![385, 1538, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), (.leaf 2 (Common.fact 68).pointIds 68), B0012, (.leaf 4 (Common.fact 69).pointIds 69), (.leaf 5 (Common.fact 70).pointIds 70), (.leaf 6 (Common.fact 71).pointIds 71)]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M6700_6900.SplitData.node0011 := by
  change Tree.branch (85 : Fin 175) _ = Tree.branch (85 : Fin 175) _
  apply congrArg (Tree.branch (85 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0012
  · rfl
  · rfl
  · rfl

def B0010 : Block := .branch 48 ![385, 1538, 9223372036854781956, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 60).pointIds 60), B0011, (.leaf 2 (Common.fact 61).pointIds 61), (.leaf 3 (Common.fact 62).pointIds 62), (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M6700_6900.SplitData.node0010 := by
  change Tree.branch (48 : Fin 175) _ = Tree.branch (48 : Fin 175) _
  apply congrArg (Tree.branch (48 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 63 ![385, 1538, 6148, 79228162514264337593543974920, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), B0010, (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M6700_6900.SplitData.node0009 := by
  change Tree.branch (63 : Fin 175) _ = Tree.branch (63 : Fin 175) _
  apply congrArg (Tree.branch (63 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 96 ![385, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), (.leaf 2 (Common.fact 50).pointIds 50), B0009, (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M6700_6900.SplitData.node0008 := by
  change Tree.branch (96 : Fin 175) _ = Tree.branch (96 : Fin 175) _
  apply congrArg (Tree.branch (96 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl

theorem accepted0008 : B0008.accepted = true := by decide +kernel
theorem checked0008 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0008 (maskNeeds ![385, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0008]
  exact B0008.sound accepted0008
#print axioms checked0008

def Tip0000_0008 : Block := .tip HexagonCover.NBand.M6700_6900.SplitData.node0008 ![385, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0008
def B0007 : Block := .branch 105 ![385, 1538, 6148, 24584, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), (.leaf 2 (Common.fact 44).pointIds 44), Tip0000_0008, (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M6700_6900.SplitData.node0007 := by
  change Tree.branch (105 : Fin 175) _ = Tree.branch (105 : Fin 175) _
  apply congrArg (Tree.branch (105 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 149 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), (.leaf 3 (Common.fact 39).pointIds 39), B0007, (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M6700_6900.SplitData.node0006 := by
  change Tree.branch (149 : Fin 175) _ = Tree.branch (149 : Fin 175) _
  apply congrArg (Tree.branch (149 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl

def B0005 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 317376877571789368527018262592] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), (.leaf 3 (Common.fact 33).pointIds 33), (.leaf 4 (Common.fact 34).pointIds 34), (.leaf 5 (Common.fact 35).pointIds 35), B0006]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M6700_6900.SplitData.node0005 := by
  change Tree.branch (134 : Fin 175) _ = Tree.branch (134 : Fin 175) _
  apply congrArg (Tree.branch (134 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0006

def B0004 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 317376877571789368527018262592] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), (.leaf 2 (Common.fact 26).pointIds 26), (.leaf 3 (Common.fact 27).pointIds 27), (.leaf 4 (Common.fact 28).pointIds 28), (.leaf 5 (Common.fact 29).pointIds 29), B0005]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M6700_6900.SplitData.node0004 := by
  change Tree.branch (110 : Fin 175) _ = Tree.branch (110 : Fin 175) _
  apply congrArg (Tree.branch (110 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0005

def B0003 : Block := .branch 99 ![385, 1538, 6148, 24584, 98320, 393248, 317376877571789368527018262592] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), (.leaf 3 (Common.fact 21).pointIds 21), (.leaf 4 (Common.fact 22).pointIds 22), (.leaf 5 (Common.fact 23).pointIds 23), B0004]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M6700_6900.SplitData.node0003 := by
  change Tree.branch (99 : Fin 175) _ = Tree.branch (99 : Fin 175) _
  apply congrArg (Tree.branch (99 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0004

def B0002 : Block := .branch 98 ![385, 1538, 6148, 24584, 98320, 393248, 464227514732018152842461248] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M6700_6900.SplitData.node0002 := by
  change Tree.branch (98 : Fin 175) _ = Tree.branch (98 : Fin 175) _
  apply congrArg (Tree.branch (98 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 88 ![385, 1538, 6148, 24584, 98320, 393248, 154742504910673084117680192] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M6700_6900.SplitData.node0001 := by
  change Tree.branch (88 : Fin 175) _ = Tree.branch (88 : Fin 175) _
  apply congrArg (Tree.branch (88 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 87 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M6700_6900.SplitData.node0000 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6700_6900.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M6700_6900.SplitTree.Run0005
