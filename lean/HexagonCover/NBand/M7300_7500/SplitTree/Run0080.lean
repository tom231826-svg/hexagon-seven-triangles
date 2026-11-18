import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0059
import HexagonCover.NBand.M7300_7500.SplitTree.Run0079
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0080
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0005_2911 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2911 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0059.checked2911
def Tip0005_4250 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4250 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0079.checked4250
def Tip0005_0011 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0011 ![385, 144116287587485186, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] HexagonCover.NBand.M7300_7500.SplitTree.Run0079.checked0011
def B2910 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 2993155353259133694351881552818361617974258139496464, 393248, 24845527856403421092721009150434039613517211369536] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 930).pointIds 930), (.leaf 5 (Common.fact 151).pointIds 151), (.leaf 6 (Common.fact 931).pointIds 931)]
theorem treeEq2910 : B2910.tree = HexagonCover.NBand.M7300_7500.SplitData.node2910 := by
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

def B2909 : Block := .branch 132 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 24845527856403421092721009150434039613517211369536] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), B2910, (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq2909 : B2909.tree = HexagonCover.NBand.M7300_7500.SplitData.node2909 := by
  change Tree.branch (132 : Fin 172) _ = Tree.branch (132 : Fin 172) _
  apply congrArg (Tree.branch (132 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2910
  · rfl
  · rfl

def B2908 : Block := .branch 135 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 24845527856403421092721009150434039613517211369536] ![(.leaf 0 (Common.fact 614).pointIds 614), (.leaf 1 (Common.fact 615).pointIds 615), (.leaf 2 (Common.fact 616).pointIds 616), (.leaf 3 (Common.fact 617).pointIds 617), (.leaf 4 (Common.fact 618).pointIds 618), B2909, (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq2908 : B2908.tree = HexagonCover.NBand.M7300_7500.SplitData.node2908 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2909
  · rfl

def B2907 : Block := .branch 90 ![748288838313422294120286634350736906063837462004097, 180143985094821378, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 24845527856403421092719771210394754233242312245312] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 927).pointIds 927), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B2908]
theorem treeEq2907 : B2907.tree = HexagonCover.NBand.M7300_7500.SplitData.node2907 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2908

def B2906 : Block := .branch 100 ![748288838313422294120286634350736906063837462004097, 180143985094821378, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 24845527856403421092719771210394754233242312245312] ![(.leaf 0 (Common.fact 869).pointIds 869), (.leaf 1 (Common.fact 926).pointIds 926), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B2907]
theorem treeEq2906 : B2906.tree = HexagonCover.NBand.M7300_7500.SplitData.node2906 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2907

def B2905 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 180143985094821378, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 24845527856403421092719771210394754233242312245312] ![(.leaf 0 (Common.fact 846).pointIds 846), (.leaf 1 (Common.fact 925).pointIds 925), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B2906]
theorem treeEq2905 : B2905.tree = HexagonCover.NBand.M7300_7500.SplitData.node2905 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2906

def B2904 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 180143985094821378, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 1461501659108974401460813886934225918747391557696] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2905]
theorem treeEq2904 : B2904.tree = HexagonCover.NBand.M7300_7500.SplitData.node2904 := by
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
  · exact treeEq2905

def B2903 : Block := .branch 169 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460813886934225918747391557696] ![B2904, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 924).pointIds 924)]
theorem treeEq2903 : B2903.tree = HexagonCover.NBand.M7300_7500.SplitData.node2903 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2904
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2902 : Block := .branch 170 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 1461501659108974402094639187048340619495743160384] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2903, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2902 : B2902.tree = HexagonCover.NBand.M7300_7500.SplitData.node2902 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2903
  · rfl

def B2901 : Block := .branch 171 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1461501659108974402094639187048340619495743160384] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2902, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 917).pointIds 917)]
theorem treeEq2901 : B2901.tree = HexagonCover.NBand.M7300_7500.SplitData.node2901 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2902
  · rfl
  · rfl

def B2900 : Block := .branch 160 ![385, 180143985094821378, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 913).pointIds 913), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2901]
theorem treeEq2900 : B2900.tree = HexagonCover.NBand.M7300_7500.SplitData.node2900 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2901

def B2899 : Block := .branch 55 ![385, 144255925564212738, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 81).pointIds 81), B2900, Tip0005_2911, (.leaf 3 (Common.fact 82).pointIds 82), (.leaf 4 (Common.fact 83).pointIds 83), (.leaf 5 (Common.fact 84).pointIds 84), (.leaf 6 (Common.fact 85).pointIds 85)]
theorem treeEq2899 : B2899.tree = HexagonCover.NBand.M7300_7500.SplitData.node2899 := by
  change Tree.branch (55 : Fin 172) _ = Tree.branch (55 : Fin 172) _
  apply congrArg (Tree.branch (55 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2900
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2898 : Block := .branch 47 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 76).pointIds 76), B2899, Tip0005_4250, (.leaf 3 (Common.fact 77).pointIds 77), (.leaf 4 (Common.fact 78).pointIds 78), (.leaf 5 (Common.fact 79).pointIds 79), (.leaf 6 (Common.fact 80).pointIds 80)]
theorem treeEq2898 : B2898.tree = HexagonCover.NBand.M7300_7500.SplitData.node2898 := by
  change Tree.branch (47 : Fin 172) _ = Tree.branch (47 : Fin 172) _
  apply congrArg (Tree.branch (47 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2899
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2897 : Block := .branch 87 ![385, 144115188075857410, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), (.leaf 2 (Common.fact 912).pointIds 912), (.leaf 3 (Common.fact 125).pointIds 125), (.leaf 4 (Common.fact 126).pointIds 126), (.leaf 5 (Common.fact 127).pointIds 127), B2898]
theorem treeEq2897 : B2897.tree = HexagonCover.NBand.M7300_7500.SplitData.node2897 := by
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
  · exact treeEq2898

def B0010 : Block := .branch 40 ![385, 144115188075857410, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] ![(.leaf 0 (Common.fact 60).pointIds 60), Tip0005_0011, B2897, (.leaf 3 (Common.fact 61).pointIds 61), (.leaf 4 (Common.fact 62).pointIds 62), (.leaf 5 (Common.fact 63).pointIds 63), (.leaf 0 [] 0)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M7300_7500.SplitData.node0010 := by
  change Tree.branch (40 : Fin 172) _ = Tree.branch (40 : Fin 172) _
  apply congrArg (Tree.branch (40 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2897
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 57 ![385, 1538, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] ![(.leaf 0 (Common.fact 54).pointIds 54), B0010, (.leaf 2 (Common.fact 55).pointIds 55), (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M7300_7500.SplitData.node0009 := by
  change Tree.branch (57 : Fin 172) _ = Tree.branch (57 : Fin 172) _
  apply congrArg (Tree.branch (57 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 48 ![385, 1538, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483890799611827146927305448226880] ![(.leaf 0 (Common.fact 48).pointIds 48), B0009, (.leaf 2 (Common.fact 49).pointIds 49), (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M7300_7500.SplitData.node0008 := by
  change Tree.branch (48 : Fin 172) _ = Tree.branch (48 : Fin 172) _
  apply congrArg (Tree.branch (48 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 98 ![385, 1538, 18446744073709557764, 79266848140492005727134572552, 98320, 393248, 21778071483573886961770089576931272425536] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), (.leaf 2 (Common.fact 44).pointIds 44), (.leaf 3 (Common.fact 45).pointIds 45), (.leaf 4 (Common.fact 46).pointIds 46), (.leaf 5 (Common.fact 47).pointIds 47), B0008]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M7300_7500.SplitData.node0007 := by
  change Tree.branch (98 : Fin 172) _ = Tree.branch (98 : Fin 172) _
  apply congrArg (Tree.branch (98 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0008

def B0006 : Block := .branch 85 ![385, 1538, 18446744073709557764, 79228162514264337593543974920, 98320, 393248, 21778071483573886961770089576931272425536] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), B0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M7300_7500.SplitData.node0006 := by
  change Tree.branch (85 : Fin 172) _ = Tree.branch (85 : Fin 172) _
  apply congrArg (Tree.branch (85 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 96 ![385, 1538, 18446744073709557764, 24584, 98320, 393248, 21778071483573886961770089576931272425536] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), B0006, (.leaf 4 (Common.fact 33).pointIds 33), (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M7300_7500.SplitData.node0005 := by
  change Tree.branch (96 : Fin 172) _ = Tree.branch (96 : Fin 172) _
  apply congrArg (Tree.branch (96 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0006
  · rfl
  · rfl
  · rfl

theorem accepted0005 : B0005.accepted = true := by decide +kernel
theorem checked0005 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0005 (maskNeeds ![385, 1538, 18446744073709557764, 24584, 98320, 393248, 21778071483573886961770089576931272425536]) := by
  rw [← treeEq0005]
  exact B0005.sound accepted0005
#print axioms checked0005

def Tip0000_0005 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0005 ![385, 1538, 18446744073709557764, 24584, 98320, 393248, 21778071483573886961770089576931272425536] checked0005
def B0004 : Block := .branch 64 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483573886961770089576931272425536] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), Tip0000_0005, (.leaf 3 (Common.fact 26).pointIds 26), (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M7300_7500.SplitData.node0004 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 105 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483573886961770089576931272425536] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), B0004, (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M7300_7500.SplitData.node0003 := by
  change Tree.branch (105 : Fin 172) _ = Tree.branch (105 : Fin 172) _
  apply congrArg (Tree.branch (105 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 633825300114114701298106892352] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M7300_7500.SplitData.node0002 := by
  change Tree.branch (134 : Fin 172) _ = Tree.branch (134 : Fin 172) _
  apply congrArg (Tree.branch (134 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 633825300114114701298106892352] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M7300_7500.SplitData.node0001 := by
  change Tree.branch (110 : Fin 172) _ = Tree.branch (110 : Fin 172) _
  apply congrArg (Tree.branch (110 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 99 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M7300_7500.SplitData.node0000 := by
  change Tree.branch (99 : Fin 172) _ = Tree.branch (99 : Fin 172) _
  apply congrArg (Tree.branch (99 : Fin 172))
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
theorem checked0000 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M7300_7500.SplitTree.Run0080
