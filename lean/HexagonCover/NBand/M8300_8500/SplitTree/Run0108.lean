import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0107
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0108
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0007_7436 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7436 ![2251799813685633, 144115188075857410, 4731607940223509469188, 81208866577120946033382549118984, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0107.checked7436
def Tip0007_7619 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7619 ![385, 146507725377897986, 4731607940223509469188, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0107.checked7619
def Tip0007_7293 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node7293 ![385, 144185556820035074, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0107.checked7293
def Tip0007_0015 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0015 ![385, 144115737831671298, 4722366482869645219844, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] HexagonCover.NBand.M8300_8500.SplitTree.Run0107.checked0015
def B7435 : Block := .branch 51 ![385, 144255925564212738, 4731607940223509469188, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![Tip0007_7436, Tip0007_7619, (.leaf 2 (Common.fact 99).pointIds 99), (.leaf 3 (Common.fact 100).pointIds 100), (.leaf 4 (Common.fact 101).pointIds 101), (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 0 [] 0)]
theorem treeEq7435 : B7435.tree = HexagonCover.NBand.M8300_8500.SplitData.node7435 := by
  change Tree.branch (51 : Fin 177) _ = Tree.branch (51 : Fin 177) _
  apply congrArg (Tree.branch (51 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7765 : Block := .branch 141 ![385, 1538, 6148, 24584, 23945242826029513411849172299223580994042798784217104, 393248, 1496577676648627976635496470064400334095056127918144] ![(.leaf 0 (Common.fact 792).pointIds 792), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 795).pointIds 795), (.leaf 4 (Common.fact 1756).pointIds 1756), (.leaf 5 (Common.fact 796).pointIds 796), (.leaf 6 (Common.fact 1785).pointIds 1785)]
theorem treeEq7765 : B7765.tree = HexagonCover.NBand.M8300_8500.SplitData.node7765 := by
  change Tree.branch (141 : Fin 177) _ = Tree.branch (141 : Fin 177) _
  apply congrArg (Tree.branch (141 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B7764 : Block := .branch 174 ![385, 144115188075857410, 4731607869854765291524, 79228162514264337593543974920, 98320, 393248, 1496577676648627976635496470064400334095056127918144] ![(.leaf 0 (Common.fact 1468).pointIds 1468), (.leaf 1 (Common.fact 1539).pointIds 1539), (.leaf 2 (Common.fact 1540).pointIds 1540), (.leaf 3 (Common.fact 1353).pointIds 1353), B7765, (.leaf 5 (Common.fact 1241).pointIds 1241), (.leaf 6 (Common.fact 1784).pointIds 1784)]
theorem treeEq7764 : B7764.tree = HexagonCover.NBand.M8300_8500.SplitData.node7764 := by
  change Tree.branch (174 : Fin 177) _ = Tree.branch (174 : Fin 177) _
  apply congrArg (Tree.branch (174 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7765
  · rfl
  · rfl

def B7763 : Block := .branch 75 ![385, 144115188075857410, 4731608010592253646852, 79228162514264337593543974920, 98320, 393248, 1496577676648627976635496470026621402232098966208576] ![(.leaf 0 (Common.fact 115).pointIds 115), (.leaf 1 (Common.fact 116).pointIds 116), (.leaf 2 (Common.fact 1783).pointIds 1783), (.leaf 3 (Common.fact 117).pointIds 117), (.leaf 4 (Common.fact 118).pointIds 118), (.leaf 5 (Common.fact 119).pointIds 119), B7764]
theorem treeEq7763 : B7763.tree = HexagonCover.NBand.M8300_8500.SplitData.node7763 := by
  change Tree.branch (75 : Fin 177) _ = Tree.branch (75 : Fin 177) _
  apply congrArg (Tree.branch (75 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7764

def B7762 : Block := .branch 82 ![385, 144115188075857410, 4731608010592253646852, 79228162514264337593543974920, 98320, 393248, 1496577676648627976635496470026621402232098966208576] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 174).pointIds 174), (.leaf 2 (Common.fact 1782).pointIds 1782), B7763, (.leaf 4 (Common.fact 175).pointIds 175), (.leaf 5 (Common.fact 176).pointIds 176), (.leaf 0 [] 0)]
theorem treeEq7762 : B7762.tree = HexagonCover.NBand.M8300_8500.SplitData.node7762 := by
  change Tree.branch (82 : Fin 177) _ = Tree.branch (82 : Fin 177) _
  apply congrArg (Tree.branch (82 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7763
  · rfl
  · rfl
  · rfl

def B7761 : Block := .branch 83 ![385, 144115188075857410, 4731608010592253646852, 79228162514264337593543974920, 98320, 393248, 1496577676648627976635496470026621402232098966208576] ![(.leaf 0 (Common.fact 177).pointIds 177), (.leaf 1 (Common.fact 178).pointIds 178), (.leaf 2 (Common.fact 1781).pointIds 1781), B7762, (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq7761 : B7761.tree = HexagonCover.NBand.M8300_8500.SplitData.node7761 := by
  change Tree.branch (83 : Fin 177) _ = Tree.branch (83 : Fin 177) _
  apply congrArg (Tree.branch (83 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7762
  · rfl
  · rfl
  · rfl

def B7760 : Block := .branch 84 ![385, 144115188075857410, 4731608010592253646852, 79228162514264337593543974920, 98320, 393248, 1496577676648627976635496470026621402232098966208576] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 1780).pointIds 1780), B7761, (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq7760 : B7760.tree = HexagonCover.NBand.M8300_8500.SplitData.node7760 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7761
  · rfl
  · rfl
  · rfl

def B7759 : Block := .branch 161 ![385, 144115188075857410, 4731608010592253646852, 79266848140492005727134572552, 98320, 393248, 1496577676648627976635496470026621402232098966208576] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 1779).pointIds 1779), (.leaf 3 (Common.fact 820).pointIds 820), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B7760]
theorem treeEq7759 : B7759.tree = HexagonCover.NBand.M8300_8500.SplitData.node7759 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq7760

def B7758 : Block := .branch 170 ![385, 144115188075857410, 4731608010592253646852, 79266848140492005727134572552, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1059).pointIds 1059), (.leaf 1 (Common.fact 1543).pointIds 1543), (.leaf 2 (Common.fact 1544).pointIds 1544), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 1062).pointIds 1062), (.leaf 5 (Common.fact 565).pointIds 565), B7759]
theorem treeEq7758 : B7758.tree = HexagonCover.NBand.M8300_8500.SplitData.node7758 := by
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
  · exact treeEq7759

def B7757 : Block := .branch 85 ![385, 144115188075857410, 4731608010592253646852, 79228162514264337593543974920, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 1778).pointIds 1778), B7758, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq7757 : B7757.tree = HexagonCover.NBand.M8300_8500.SplitData.node7757 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq7758
  · rfl
  · rfl
  · rfl

def B7434 : Block := .branch 47 ![385, 144115188075857410, 4731607940223509469188, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 1563).pointIds 1563), B7435, B7757, (.leaf 3 (Common.fact 1564).pointIds 1564), (.leaf 4 (Common.fact 1565).pointIds 1565), (.leaf 5 (Common.fact 1566).pointIds 1566), (.leaf 6 (Common.fact 1567).pointIds 1567)]
theorem treeEq7434 : B7434.tree = HexagonCover.NBand.M8300_8500.SplitData.node7434 := by
  change Tree.branch (47 : Fin 177) _ = Tree.branch (47 : Fin 177) _
  apply congrArg (Tree.branch (47 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq7435
  · exact treeEq7757
  · rfl
  · rfl
  · rfl
  · rfl

def B7292 : Block := .branch 46 ![385, 144115188075857410, 4731607869854765291524, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 94).pointIds 94), Tip0007_7293, B7434, (.leaf 3 (Common.fact 95).pointIds 95), (.leaf 4 (Common.fact 96).pointIds 96), (.leaf 5 (Common.fact 97).pointIds 97), (.leaf 6 (Common.fact 98).pointIds 98)]
theorem treeEq7292 : B7292.tree = HexagonCover.NBand.M8300_8500.SplitData.node7292 := by
  change Tree.branch (46 : Fin 177) _ = Tree.branch (46 : Fin 177) _
  apply congrArg (Tree.branch (46 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7434
  · rfl
  · rfl
  · rfl
  · rfl

def B0014 : Block := .branch 39 ![385, 144115188075857410, 4731607869305009477636, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 84).pointIds 84), Tip0007_0015, B7292, (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), (.leaf 5 (Common.fact 87).pointIds 87), (.leaf 0 [] 0)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M8300_8500.SplitData.node0014 := by
  change Tree.branch (39 : Fin 177) _ = Tree.branch (39 : Fin 177) _
  apply congrArg (Tree.branch (39 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq7292
  · rfl
  · rfl
  · rfl
  · rfl

def B0013 : Block := .branch 72 ![385, 144115188075857410, 9241386435364263940, 81248480658378078202179321094152, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 78).pointIds 78), (.leaf 1 (Common.fact 79).pointIds 79), B0014, (.leaf 3 (Common.fact 80).pointIds 80), (.leaf 4 (Common.fact 81).pointIds 81), (.leaf 5 (Common.fact 82).pointIds 82), (.leaf 6 (Common.fact 83).pointIds 83)]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M8300_8500.SplitData.node0013 := by
  change Tree.branch (72 : Fin 177) _ = Tree.branch (72 : Fin 177) _
  apply congrArg (Tree.branch (72 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0014
  · rfl
  · rfl
  · rfl
  · rfl

def B0012 : Block := .branch 96 ![385, 144115188075857410, 9241386435364263940, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 72).pointIds 72), (.leaf 1 (Common.fact 73).pointIds 73), (.leaf 2 (Common.fact 74).pointIds 74), B0013, (.leaf 4 (Common.fact 75).pointIds 75), (.leaf 5 (Common.fact 76).pointIds 76), (.leaf 6 (Common.fact 77).pointIds 77)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M8300_8500.SplitData.node0012 := by
  change Tree.branch (96 : Fin 177) _ = Tree.branch (96 : Fin 177) _
  apply congrArg (Tree.branch (96 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0013
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 54 ![385, 144115188075857410, 9223372036854781956, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 66).pointIds 66), (.leaf 1 (Common.fact 67).pointIds 67), B0012, (.leaf 3 (Common.fact 68).pointIds 68), (.leaf 4 (Common.fact 69).pointIds 69), (.leaf 5 (Common.fact 70).pointIds 70), (.leaf 6 (Common.fact 71).pointIds 71)]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M8300_8500.SplitData.node0011 := by
  change Tree.branch (54 : Fin 177) _ = Tree.branch (54 : Fin 177) _
  apply congrArg (Tree.branch (54 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0012
  · rfl
  · rfl
  · rfl
  · rfl

def B0010 : Block := .branch 57 ![385, 1538, 9223372036854781956, 81169252495863813864585777143816, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 60).pointIds 60), B0011, (.leaf 2 (Common.fact 61).pointIds 61), (.leaf 3 (Common.fact 62).pointIds 62), (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M8300_8500.SplitData.node0010 := by
  change Tree.branch (57 : Fin 177) _ = Tree.branch (57 : Fin 177) _
  apply congrArg (Tree.branch (57 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 95 ![385, 1538, 9223372036854781956, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), (.leaf 2 (Common.fact 56).pointIds 56), B0010, (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M8300_8500.SplitData.node0009 := by
  change Tree.branch (95 : Fin 177) _ = Tree.branch (95 : Fin 177) _
  apply congrArg (Tree.branch (95 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 63 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), B0009, (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M8300_8500.SplitData.node0008 := by
  change Tree.branch (63 : Fin 177) _ = Tree.branch (63 : Fin 177) _
  apply congrArg (Tree.branch (63 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 106 ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 42).pointIds 42), (.leaf 1 (Common.fact 43).pointIds 43), (.leaf 2 (Common.fact 44).pointIds 44), B0008, (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M8300_8500.SplitData.node0007 := by
  change Tree.branch (106 : Fin 177) _ = Tree.branch (106 : Fin 177) _
  apply congrArg (Tree.branch (106 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl

theorem accepted0007 : B0007.accepted = true := by decide +kernel
theorem checked0007 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0007 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325147590104424042201152]) := by
  rw [← treeEq0007]
  exact B0007.sound accepted0007
#print axioms checked0007

def Tip0000_0007 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0007 ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325147590104424042201152] checked0007
def B0006 : Block := .branch 117 ![385, 1538, 6148, 24584, 98320, 393248, 21783388394923201325147590104424042201152] ![(.leaf 0 (Common.fact 36).pointIds 36), (.leaf 1 (Common.fact 37).pointIds 37), (.leaf 2 (Common.fact 38).pointIds 38), Tip0000_0007, (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M8300_8500.SplitData.node0006 := by
  change Tree.branch (117 : Fin 177) _ = Tree.branch (117 : Fin 177) _
  apply congrArg (Tree.branch (117 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), (.leaf 2 (Common.fact 32).pointIds 32), (.leaf 3 (Common.fact 33).pointIds 33), (.leaf 4 (Common.fact 34).pointIds 34), (.leaf 5 (Common.fact 35).pointIds 35), B0006]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M8300_8500.SplitData.node0005 := by
  change Tree.branch (134 : Fin 177) _ = Tree.branch (134 : Fin 177) _
  apply congrArg (Tree.branch (134 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0006

def B0004 : Block := .branch 48 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 24).pointIds 24), B0005, (.leaf 2 (Common.fact 25).pointIds 25), (.leaf 3 (Common.fact 26).pointIds 26), (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M8300_8500.SplitData.node0004 := by
  change Tree.branch (48 : Fin 177) _ = Tree.branch (48 : Fin 177) _
  apply congrArg (Tree.branch (48 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 49 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 18).pointIds 18), B0004, (.leaf 2 (Common.fact 19).pointIds 19), (.leaf 3 (Common.fact 20).pointIds 20), (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M8300_8500.SplitData.node0003 := by
  change Tree.branch (49 : Fin 177) _ = Tree.branch (49 : Fin 177) _
  apply congrArg (Tree.branch (49 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 53 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), B0003, (.leaf 3 (Common.fact 14).pointIds 14), (.leaf 4 (Common.fact 15).pointIds 15), (.leaf 5 (Common.fact 16).pointIds 16), (.leaf 6 (Common.fact 17).pointIds 17)]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M8300_8500.SplitData.node0002 := by
  change Tree.branch (53 : Fin 177) _ = Tree.branch (53 : Fin 177) _
  apply congrArg (Tree.branch (53 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0003
  · rfl
  · rfl
  · rfl
  · rfl

def B0001 : Block := .branch 62 ![385, 1538, 6148, 24584, 98320, 393248, 5316911983139663491615228790876667968] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), B0002, (.leaf 3 (Common.fact 8).pointIds 8), (.leaf 4 (Common.fact 9).pointIds 9), (.leaf 5 (Common.fact 10).pointIds 10), (.leaf 6 (Common.fact 11).pointIds 11)]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M8300_8500.SplitData.node0001 := by
  change Tree.branch (62 : Fin 177) _ = Tree.branch (62 : Fin 177) _
  apply congrArg (Tree.branch (62 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0002
  · rfl
  · rfl
  · rfl
  · rfl

def B0000 : Block := .branch 122 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), B0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M8300_8500.SplitData.node0000 := by
  change Tree.branch (122 : Fin 177) _ = Tree.branch (122 : Fin 177) _
  apply congrArg (Tree.branch (122 : Fin 177))
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
theorem checked0000 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M8300_8500.SplitTree.Run0108
