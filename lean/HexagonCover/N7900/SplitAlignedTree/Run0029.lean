import HexagonCover.N7900.SplitAlignedTree.Run0028
import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0029
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def Tip0000_0013 : Block := .tip HexagonCover.N7900.SplitData.node0013 ![10141204801825835211973625643393, 144115188075857410, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.N7900.SplitAlignedTree.Run0028.checked0013
def B0012 : Block := .branch 103 ![385, 144115188075857410, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![Tip0000_0013, (.leaf 1 (Common.fact 72).pointIds 72), (.leaf 2 (Common.fact 73).pointIds 73), (.leaf 3 (Common.fact 74).pointIds 74), (.leaf 4 (Common.fact 75).pointIds 75), (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.N7900.SplitData.node0012 := by
  change Tree.branch (103 : Fin 170) _ = Tree.branch (103 : Fin 170) _
  apply congrArg (Tree.branch (103 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 98 ![385, 144115188075857410, 9241456804108441604, 79266848140492005727134572552, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), (.leaf 2 (Common.fact 68).pointIds 68), (.leaf 3 (Common.fact 69).pointIds 69), (.leaf 4 (Common.fact 70).pointIds 70), (.leaf 5 (Common.fact 71).pointIds 71), B0012]
theorem treeEq0011 : B0011.tree = HexagonCover.N7900.SplitData.node0011 := by
  change Tree.branch (98 : Fin 170) _ = Tree.branch (98 : Fin 170) _
  apply congrArg (Tree.branch (98 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0012

def B0010 : Block := .branch 85 ![385, 144115188075857410, 9241456804108441604, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 60).pointIds 60), (.leaf 1 (Common.fact 61).pointIds 61), (.leaf 2 (Common.fact 62).pointIds 62), B0011, (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.N7900.SplitData.node0010 := by
  change Tree.branch (85 : Fin 170) _ = Tree.branch (85 : Fin 170) _
  apply congrArg (Tree.branch (85 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 46 ![385, 144115188075857410, 9241386435364263940, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), B0010, (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.N7900.SplitData.node0009 := by
  change Tree.branch (46 : Fin 170) _ = Tree.branch (46 : Fin 170) _
  apply congrArg (Tree.branch (46 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 96 ![385, 144115188075857410, 9241386435364263940, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), (.leaf 2 (Common.fact 50).pointIds 50), B0009, (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.N7900.SplitData.node0008 := by
  change Tree.branch (96 : Fin 170) _ = Tree.branch (96 : Fin 170) _
  apply congrArg (Tree.branch (96 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 54 ![385, 144115188075857410, 9223372036854781956, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), B0008, (.leaf 3 (Common.fact 44).pointIds 44), (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.N7900.SplitData.node0007 := by
  change Tree.branch (54 : Fin 170) _ = Tree.branch (54 : Fin 170) _
  apply congrArg (Tree.branch (54 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 57 ![385, 1538, 9223372036854781956, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 36).pointIds 36), B0007, (.leaf 2 (Common.fact 37).pointIds 37), (.leaf 3 (Common.fact 38).pointIds 38), (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.N7900.SplitData.node0006 := by
  change Tree.branch (57 : Fin 170) _ = Tree.branch (57 : Fin 170) _
  apply congrArg (Tree.branch (57 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 63 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), B0006, (.leaf 3 (Common.fact 32).pointIds 32), (.leaf 4 (Common.fact 33).pointIds 33), (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.N7900.SplitData.node0005 := by
  change Tree.branch (63 : Fin 170) _ = Tree.branch (63 : Fin 170) _
  apply congrArg (Tree.branch (63 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0006
  · rfl
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 106 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), (.leaf 2 (Common.fact 26).pointIds 26), B0005, (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.N7900.SplitData.node0004 := by
  change Tree.branch (106 : Fin 170) _ = Tree.branch (106 : Fin 170) _
  apply congrArg (Tree.branch (106 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0005
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 117 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), B0004, (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.N7900.SplitData.node0003 := by
  change Tree.branch (117 : Fin 170) _ = Tree.branch (117 : Fin 170) _
  apply congrArg (Tree.branch (117 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.N7900.SplitData.node0002 := by
  change Tree.branch (134 : Fin 170) _ = Tree.branch (134 : Fin 170) _
  apply congrArg (Tree.branch (134 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 45 ![385, 1538, 6148, 24584, 98320, 393248, 1298074214633706907133173837594688] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), B0002, (.leaf 3 (Common.fact 8).pointIds 8), (.leaf 4 (Common.fact 9).pointIds 9), (.leaf 5 (Common.fact 10).pointIds 10), (.leaf 6 (Common.fact 11).pointIds 11)]
theorem treeEq0001 : B0001.tree = HexagonCover.N7900.SplitData.node0001 := by
  change Tree.branch (45 : Fin 170) _ = Tree.branch (45 : Fin 170) _
  apply congrArg (Tree.branch (45 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0002
  · rfl
  · rfl
  · rfl
  · rfl

def B0000 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.N7900.SplitData.node0000 := by
  change Tree.branch (110 : Fin 170) _ = Tree.branch (110 : Fin 170) _
  apply congrArg (Tree.branch (110 : Fin 170))
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
theorem checked0000 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.N7900.SplitAlignedTree.Run0029
