import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0007
import HexagonCover.NBand.M7100_7300.SplitTree.Run0009
import HexagonCover.NBand.M7100_7300.SplitTree.Run0010
import HexagonCover.NBand.M7100_7300.SplitTree.Run0015
import HexagonCover.NBand.M7100_7300.SplitTree.Run0017
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0018
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0012_0515 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0515 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0007.checked0515
def Tip0012_0648 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0648 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0009.checked0648
def Tip0012_0015 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0015 ![385, 144257025075840514, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] HexagonCover.NBand.M7100_7300.SplitTree.Run0010.checked0015
def Tip0012_1083 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1083 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0015.checked1083
def Tip0012_1216 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node1216 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0017.checked1216
def Tip0012_0792 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0792 ![385, 144255925564212738, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0017.checked0792
def B0511 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M7100_7300.SplitData.node0511 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0510 : Block := .branch 168 ![288230376151712129, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0511]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M7100_7300.SplitData.node0510 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0511

def B0514 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M7100_7300.SplitData.node0514 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0513 : Block := .branch 168 ![576460752303423873, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0514]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M7100_7300.SplitData.node0513 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0514

def B0512 : Block := .branch 59 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0513, Tip0012_0515, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M7100_7300.SplitData.node0512 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0513
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0509 : Block := .branch 58 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0510, B0512, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M7100_7300.SplitData.node0509 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0510
  · exact treeEq0512
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0508 : Block := .branch 56 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 159).pointIds 159), B0509, Tip0012_0648, (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), (.leaf 6 (Common.fact 163).pointIds 163)]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M7100_7300.SplitData.node0508 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0507 : Block := .branch 87 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0508]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M7100_7300.SplitData.node0507 := by
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
  · exact treeEq0508

def B0014 : Block := .branch 47 ![385, 144116287587485186, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 82).pointIds 82), Tip0012_0015, B0507, (.leaf 3 (Common.fact 83).pointIds 83), (.leaf 4 (Common.fact 84).pointIds 84), (.leaf 5 (Common.fact 85).pointIds 85), (.leaf 6 (Common.fact 86).pointIds 86)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M7100_7300.SplitData.node0014 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0507
  · rfl
  · rfl
  · rfl
  · rfl

def B1079 : Block := .branch 102 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M7100_7300.SplitData.node1079 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1078 : Block := .branch 168 ![288230376151712129, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1079]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M7100_7300.SplitData.node1078 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1079

def B1082 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 810).pointIds 810), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M7100_7300.SplitData.node1082 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1081 : Block := .branch 168 ![576460752303423873, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 920).pointIds 920), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1082]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M7100_7300.SplitData.node1081 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1082

def B1080 : Block := .branch 59 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B1081, Tip0012_1083, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M7100_7300.SplitData.node1080 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1081
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1077 : Block := .branch 58 ![385, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B1078, B1080, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M7100_7300.SplitData.node1077 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1078
  · exact treeEq1080
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1076 : Block := .branch 56 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 159).pointIds 159), B1077, Tip0012_1216, (.leaf 3 (Common.fact 160).pointIds 160), (.leaf 4 (Common.fact 161).pointIds 161), (.leaf 5 (Common.fact 162).pointIds 162), (.leaf 6 (Common.fact 163).pointIds 163)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M7100_7300.SplitData.node1076 := by
  change Tree.branch (56 : Fin 173) _ = Tree.branch (56 : Fin 173) _
  apply congrArg (Tree.branch (56 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1077
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0791 : Block := .branch 47 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 82).pointIds 82), Tip0012_0792, B1076, (.leaf 3 (Common.fact 83).pointIds 83), (.leaf 4 (Common.fact 84).pointIds 84), (.leaf 5 (Common.fact 85).pointIds 85), (.leaf 6 (Common.fact 86).pointIds 86)]
theorem treeEq0791 : B0791.tree = HexagonCover.NBand.M7100_7300.SplitData.node0791 := by
  change Tree.branch (47 : Fin 173) _ = Tree.branch (47 : Fin 173) _
  apply congrArg (Tree.branch (47 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1076
  · rfl
  · rfl
  · rfl
  · rfl

def B0790 : Block := .branch 87 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 892).pointIds 892), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), (.leaf 5 (Common.fact 133).pointIds 133), B0791]
theorem treeEq0790 : B0790.tree = HexagonCover.NBand.M7100_7300.SplitData.node0790 := by
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
  · exact treeEq0791

def B0013 : Block := .branch 40 ![385, 144115188075857410, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 78).pointIds 78), B0014, B0790, (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), (.leaf 0 [] 0)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M7100_7300.SplitData.node0013 := by
  change Tree.branch (40 : Fin 173) _ = Tree.branch (40 : Fin 173) _
  apply congrArg (Tree.branch (40 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0014
  · exact treeEq0790
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 57 ![385, 1538, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 72).pointIds 72), B0013, (.leaf 2 (Common.fact 73).pointIds 73), (.leaf 3 (Common.fact 74).pointIds 74), (.leaf 4 (Common.fact 75).pointIds 75), (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M7100_7300.SplitData.node0012 := by
  change Tree.branch (57 : Fin 173) _ = Tree.branch (57 : Fin 173) _
  apply congrArg (Tree.branch (57 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0013
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0012 : B0012.accepted = true := by decide +kernel
theorem checked0012 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0012 (maskNeeds ![385, 1538, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248]) := by
  rw [← treeEq0012]
  exact B0012.sound accepted0012
#print axioms checked0012

def Tip0000_0012 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0012 ![385, 1538, 18446744073709557764, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] checked0012
def B0011 : Block := .branch 64 ![385, 1538, 6148, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), Tip0000_0012, (.leaf 3 (Common.fact 68).pointIds 68), (.leaf 4 (Common.fact 69).pointIds 69), (.leaf 5 (Common.fact 70).pointIds 70), (.leaf 6 (Common.fact 71).pointIds 71)]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M7100_7300.SplitData.node0011 := by
  change Tree.branch (64 : Fin 173) _ = Tree.branch (64 : Fin 173) _
  apply congrArg (Tree.branch (64 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0010 : Block := .branch 48 ![385, 1538, 9223372036854781956, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 60).pointIds 60), B0011, (.leaf 2 (Common.fact 61).pointIds 61), (.leaf 3 (Common.fact 62).pointIds 62), (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M7100_7300.SplitData.node0010 := by
  change Tree.branch (48 : Fin 173) _ = Tree.branch (48 : Fin 173) _
  apply congrArg (Tree.branch (48 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 63 ![385, 1538, 6148, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), B0010, (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M7100_7300.SplitData.node0009 := by
  change Tree.branch (63 : Fin 173) _ = Tree.branch (63 : Fin 173) _
  apply congrArg (Tree.branch (63 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 149 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), (.leaf 2 (Common.fact 50).pointIds 50), (.leaf 3 (Common.fact 51).pointIds 51), B0009, (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M7100_7300.SplitData.node0008 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl

def B0007 : Block := .branch 98 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), (.leaf 2 (Common.fact 44).pointIds 44), (.leaf 3 (Common.fact 45).pointIds 45), (.leaf 4 (Common.fact 46).pointIds 46), (.leaf 5 (Common.fact 47).pointIds 47), B0008]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M7100_7300.SplitData.node0007 := by
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
  · exact treeEq0008

def B0006 : Block := .branch 85 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), B0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M7100_7300.SplitData.node0006 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 105 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), B0006, (.leaf 4 (Common.fact 33).pointIds 33), (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M7100_7300.SplitData.node0005 := by
  change Tree.branch (105 : Fin 173) _ = Tree.branch (105 : Fin 173) _
  apply congrArg (Tree.branch (105 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0006
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 148 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), (.leaf 2 (Common.fact 26).pointIds 26), (.leaf 3 (Common.fact 27).pointIds 27), B0005, (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M7100_7300.SplitData.node0004 := by
  change Tree.branch (148 : Fin 173) _ = Tree.branch (148 : Fin 173) _
  apply congrArg (Tree.branch (148 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0005
  · rfl
  · rfl

def B0003 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 309485009821345618480070720] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), (.leaf 3 (Common.fact 21).pointIds 21), (.leaf 4 (Common.fact 22).pointIds 22), (.leaf 5 (Common.fact 23).pointIds 23), B0004]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M7100_7300.SplitData.node0003 := by
  change Tree.branch (134 : Fin 173) _ = Tree.branch (134 : Fin 173) _
  apply congrArg (Tree.branch (134 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0004

def B0002 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 309485009821345618480070720] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M7100_7300.SplitData.node0002 := by
  change Tree.branch (110 : Fin 173) _ = Tree.branch (110 : Fin 173) _
  apply congrArg (Tree.branch (110 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 99 ![385, 1538, 6148, 24584, 98320, 393248, 309485009821345618480070720] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), (.leaf 2 (Common.fact 8).pointIds 8), (.leaf 3 (Common.fact 9).pointIds 9), (.leaf 4 (Common.fact 10).pointIds 10), (.leaf 5 (Common.fact 11).pointIds 11), B0002]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M7100_7300.SplitData.node0001 := by
  change Tree.branch (99 : Fin 173) _ = Tree.branch (99 : Fin 173) _
  apply congrArg (Tree.branch (99 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0002

def B0000 : Block := .branch 88 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M7100_7300.SplitData.node0000 := by
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
  · exact treeEq0001

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M7100_7300.SplitTree.Run0018
