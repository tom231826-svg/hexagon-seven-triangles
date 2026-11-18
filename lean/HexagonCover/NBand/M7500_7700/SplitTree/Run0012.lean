import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0006
import HexagonCover.NBand.M7500_7700.SplitTree.Run0009
import HexagonCover.NBand.M7500_7700.SplitTree.Run0011
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0012
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0595_0760 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0760 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0009.checked0760
def Tip0595_0596 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0596 ![590295810358705652097, 148294669267544049154, 7138998042916653373444, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0009.checked0596
def B0839 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M7500_7700.SplitData.node0839 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0838 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0839, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M7500_7700.SplitData.node0838 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0839
  · rfl

def B0837 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B0838, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M7500_7700.SplitData.node0837 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0838
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0836 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0837, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M7500_7700.SplitData.node0836 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0837
  · rfl

def B0835 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 38690348594151003235835912, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 856).pointIds 856), B0836, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M7500_7700.SplitData.node0835 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0836
  · rfl
  · rfl

def B0759 : Block := .branch 68 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), Tip0595_0760, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B0835]
theorem treeEq0759 : B0759.tree = HexagonCover.NBand.M7500_7700.SplitData.node0759 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0835

def B0758 : Block := .branch 113 ![590295810358705652097, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![B0759, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0758 : B0758.tree = HexagonCover.NBand.M7500_7700.SplitData.node0758 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0759
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0757 : Block := .branch 144 ![590295810358705652097, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0758, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq0757 : B0757.tree = HexagonCover.NBand.M7500_7700.SplitData.node0757 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0758
  · rfl

def B0756 : Block := .branch 149 ![590295810358705652097, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0757, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0756 : B0756.tree = HexagonCover.NBand.M7500_7700.SplitData.node0756 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0757
  · rfl
  · rfl

def B0755 : Block := .branch 161 ![590295810358705652097, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 854).pointIds 854), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0756]
theorem treeEq0755 : B0755.tree = HexagonCover.NBand.M7500_7700.SplitData.node0755 := by
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
  · exact treeEq0756

def B0595 : Block := .branch 72 ![590295810358705652097, 148294669267544049154, 2416631560047008159748, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), Tip0595_0596, B0755, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M7500_7700.SplitData.node0595 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0755
  · rfl
  · rfl
  · rfl

theorem accepted0595 : B0595.accepted = true := by decide +kernel
theorem checked0595 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0595 (maskNeeds ![590295810358705652097, 148294669267544049154, 2416631560047008159748, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0595]
  exact B0595.sound accepted0595
#print axioms checked0595

def Tip0592_0846 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0846 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0011.checked0846
def Tip0592_0921 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0921 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0011.checked0921
def Tip0592_0595 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0595 ![590295810358705652097, 148294669267544049154, 2416631560047008159748, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked0595
def B0845 : Block := .branch 72 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), Tip0592_0846, Tip0592_0921, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M7500_7700.SplitData.node0845 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1000 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq1000 : B1000.tree = HexagonCover.NBand.M7500_7700.SplitData.node1000 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0999 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B1000, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0999 : B0999.tree = HexagonCover.NBand.M7500_7700.SplitData.node0999 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1000
  · rfl

def B0998 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B0999, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0998 : B0998.tree = HexagonCover.NBand.M7500_7700.SplitData.node0998 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0997 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0998, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0997 : B0997.tree = HexagonCover.NBand.M7500_7700.SplitData.node0997 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0998
  · rfl

def B0996 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 38687987410909568413229064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 859).pointIds 859), B0997, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0996 : B0996.tree = HexagonCover.NBand.M7500_7700.SplitData.node0996 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0997
  · rfl
  · rfl

def B0844 : Block := .branch 68 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), B0845, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B0996]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M7500_7700.SplitData.node0844 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0845
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0996

def B0843 : Block := .branch 113 ![590295810358705652097, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![B0844, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M7500_7700.SplitData.node0843 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0844
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0842 : Block := .branch 144 ![590295810358705652097, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0843, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M7500_7700.SplitData.node0842 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl

def B0841 : Block := .branch 149 ![590295810358705652097, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0842, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M7500_7700.SplitData.node0841 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0842
  · rfl
  · rfl

def B0840 : Block := .branch 161 ![590295810358705652097, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 857).pointIds 857), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0841]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M7500_7700.SplitData.node0840 := by
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
  · exact treeEq0841

def B0594 : Block := .branch 71 ![590295810358705652097, 148294669267544049154, 55448318612185552900, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), Tip0592_0595, B0840, (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M7500_7700.SplitData.node0594 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0840
  · rfl
  · rfl
  · rfl

def B1002 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1002 : B1002.tree = HexagonCover.NBand.M7500_7700.SplitData.node1002 := by
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

def B1001 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B1002, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1001 : B1001.tree = HexagonCover.NBand.M7500_7700.SplitData.node1001 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1002
  · rfl
  · rfl

def B0593 : Block := .branch 69 ![385, 148294669267544049154, 55448318612185552900, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B0594, (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), B1001]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M7500_7700.SplitData.node0593 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0594
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1001

def B1006 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq1006 : B1006.tree = HexagonCover.NBand.M7500_7700.SplitData.node1006 := by
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

def B1005 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B1006, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq1005 : B1005.tree = HexagonCover.NBand.M7500_7700.SplitData.node1005 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1006
  · rfl
  · rfl

def B1004 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B1005, (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq1004 : B1004.tree = HexagonCover.NBand.M7500_7700.SplitData.node1004 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1005
  · rfl

def B1003 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B1004, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1003 : B1003.tree = HexagonCover.NBand.M7500_7700.SplitData.node1003 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1004
  · rfl
  · rfl

def B0592 : Block := .branch 67 ![385, 720716677867636226, 55448318612185552900, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 233).pointIds 233), B0593, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), B1003]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M7500_7700.SplitData.node0592 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0593
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1003

theorem accepted0592 : B0592.accepted = true := by decide +kernel
theorem checked0592 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0592 (maskNeeds ![385, 720716677867636226, 55448318612185552900, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0592]
  exact B0592.sound accepted0592
#print axioms checked0592

def Tip0591_0592 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0592 ![385, 720716677867636226, 55448318612185552900, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked0592
def B1021 : Block := .branch 79 ![2244866514940266882360859903052210718191512386011521, 1461501637330902918203684832716283019655932544514, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 863).pointIds 863), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M7500_7700.SplitData.node1021 := by
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

def B1020 : Block := .branch 170 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 38685626227668133590622216, 98320, 2993155353253731711777011654710880546081278819434528, 21778071483256974311749925714704515727424] ![B1021, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 773).pointIds 773), (.leaf 6 (Common.fact 862).pointIds 862)]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M7500_7700.SplitData.node1020 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1019 : Block := .branch 171 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 38685626227668133590622216, 182698855038962130087031371948671701637744656400, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 772).pointIds 772), B1020, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M7500_7700.SplitData.node1019 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1020
  · rfl

def B1018 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), B1019, (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M7500_7700.SplitData.node1018 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1019
  · rfl
  · rfl

def B1017 : Block := .branch 129 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 698).pointIds 698), (.leaf 5 (Common.fact 263).pointIds 263), B1018]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M7500_7700.SplitData.node1017 := by
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
  · exact treeEq1018

def B1016 : Block := .branch 130 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 256).pointIds 256), B1017]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M7500_7700.SplitData.node1016 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1017

def B1015 : Block := .branch 131 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 560).pointIds 560), B1016]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M7500_7700.SplitData.node1015 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1016

def B1014 : Block := .branch 163 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 284).pointIds 284), B1015]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M7500_7700.SplitData.node1014 := by
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
  · exact treeEq1015

def B1013 : Block := .branch 151 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B1014, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1013 : B1013.tree = HexagonCover.NBand.M7500_7700.SplitData.node1013 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1014
  · rfl
  · rfl

def B1012 : Block := .branch 132 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 219).pointIds 219), B1013]
theorem treeEq1012 : B1012.tree = HexagonCover.NBand.M7500_7700.SplitData.node1012 := by
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
  · exact treeEq1013

def B1011 : Block := .branch 133 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 693).pointIds 693), (.leaf 5 (Common.fact 198).pointIds 198), B1012]
theorem treeEq1011 : B1011.tree = HexagonCover.NBand.M7500_7700.SplitData.node1011 := by
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
  · exact treeEq1012

def B1010 : Block := .branch 157 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 98320, 42535295865117307932921825928971419680, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B1011, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq1010 : B1010.tree = HexagonCover.NBand.M7500_7700.SplitData.node1010 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1011
  · rfl
  · rfl

def B1009 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 691).pointIds 691), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B1010, (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq1009 : B1009.tree = HexagonCover.NBand.M7500_7700.SplitData.node1009 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1010
  · rfl

def B1008 : Block := .branch 169 ![385, 1461501637330902918203684832716427275581496755714, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054254836387238878117952] ![B1009, (.leaf 1 (Common.fact 861).pointIds 861), (.leaf 2 (Common.fact 732).pointIds 732), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq1008 : B1008.tree = HexagonCover.NBand.M7500_7700.SplitData.node1008 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1009
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1007 : Block := .branch 160 ![385, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054254836387238878117952] ![(.leaf 0 (Common.fact 362).pointIds 362), B1008, (.leaf 2 (Common.fact 735).pointIds 735), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq1007 : B1007.tree = HexagonCover.NBand.M7500_7700.SplitData.node1007 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1008
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0591 : Block := .branch 65 ![385, 720716677867636226, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), Tip0591_0592, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B1007]
theorem treeEq0591 : B0591.tree = HexagonCover.NBand.M7500_7700.SplitData.node0591 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1007

theorem accepted0591 : B0591.accepted = true := by decide +kernel
theorem checked0591 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0591 (maskNeeds ![385, 720716677867636226, 18554830464766449668, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0591]
  exact B0591.sound accepted0591
#print axioms checked0591

def B0580 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993338041306804683072962984593532757642937488211984, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 588).pointIds 588), (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 213).pointIds 213)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M7500_7700.SplitData.node0580 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0579 : Block := .branch 171 ![385, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 1496577676626844609009760702840784326249660241281056, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), B0580, (.leaf 5 (Common.fact 730).pointIds 730), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M7500_7700.SplitData.node0579 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0580
  · rfl
  · rfl

def B0578 : Block := .branch 170 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), B0579, (.leaf 6 (Common.fact 725).pointIds 725)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M7500_7700.SplitData.node0578 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0579
  · rfl

def B0577 : Block := .branch 88 ![288230376151712129, 302231599159582857889282, 18518801667747485700, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0578]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M7500_7700.SplitData.node0577 := by
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
  · exact treeEq0578

def B0576 : Block := .branch 78 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 142).pointIds 142), B0577, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 199).pointIds 199)]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M7500_7700.SplitData.node0576 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0577
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0575 : Block := .branch 133 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 182688053115506591816447190585133387587640197136, 20769187434139310514121985317273632, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0576]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M7500_7700.SplitData.node0575 := by
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
  · exact treeEq0576

def B0574 : Block := .branch 157 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0575, (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 0 [] 0)]
theorem treeEq0574 : B0574.tree = HexagonCover.NBand.M7500_7700.SplitData.node0574 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0575
  · rfl
  · rfl

def B0573 : Block := .branch 114 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 184).pointIds 184), (.leaf 3 (Common.fact 185).pointIds 185), (.leaf 4 (Common.fact 186).pointIds 186), B0574, (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0573 : B0573.tree = HexagonCover.NBand.M7500_7700.SplitData.node0573 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0574
  · rfl

def B0572 : Block := .branch 65 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0573, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0572 : B0572.tree = HexagonCover.NBand.M7500_7700.SplitData.node0572 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0573
  · rfl
  · rfl
  · rfl
  · rfl

def B0571 : Block := .branch 67 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 233).pointIds 233), B0572, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0571 : B0571.tree = HexagonCover.NBand.M7500_7700.SplitData.node0571 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0572
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0570 : Block := .branch 122 ![288230376151712129, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B0571]
theorem treeEq0570 : B0570.tree = HexagonCover.NBand.M7500_7700.SplitData.node0570 := by
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
  · exact treeEq0571

def B0569 : Block := .branch 138 ![288230376151712129, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0570, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 716).pointIds 716)]
theorem treeEq0569 : B0569.tree = HexagonCover.NBand.M7500_7700.SplitData.node0569 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0570
  · rfl
  · rfl

def B0568 : Block := .branch 144 ![288230376151712129, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0569, (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0568 : B0568.tree = HexagonCover.NBand.M7500_7700.SplitData.node0568 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0569
  · rfl

def B0567 : Block := .branch 124 ![288230376151712129, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0568]
theorem treeEq0567 : B0567.tree = HexagonCover.NBand.M7500_7700.SplitData.node0567 := by
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
  · exact treeEq0568

theorem accepted0567 : B0567.accepted = true := by decide +kernel
theorem checked0567 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0567 (maskNeeds ![288230376151712129, 144255925564212738, 18518801667747485700, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0567]
  exact B0567.sound accepted0567
#print axioms checked0567

def Tip0030_0047 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0047 ![385, 504403158265497090, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.NBand.M7500_7700.SplitTree.Run0006.checked0047
def B0046 : Block := .branch 79 ![288230376151712129, 216172782113785346, 6148, 24584, 98320, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 220).pointIds 220), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 226).pointIds 226)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M7500_7700.SplitData.node0046 := by
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

def B0045 : Block := .branch 132 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 21799339131189997193194225157124669308992] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), B0046]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M7500_7700.SplitData.node0045 := by
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
  · exact treeEq0046

def B0044 : Block := .branch 141 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B0045, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 213).pointIds 213)]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M7500_7700.SplitData.node0044 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045
  · rfl
  · rfl

def B0043 : Block := .branch 149 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0044, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 212).pointIds 212)]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M7500_7700.SplitData.node0043 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0044
  · rfl
  · rfl

def B0042 : Block := .branch 166 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 32688374872660028024022212594941252075584] ![(.leaf 0 (Common.fact 206).pointIds 206), (.leaf 1 (Common.fact 207).pointIds 207), (.leaf 2 (Common.fact 208).pointIds 208), (.leaf 3 (Common.fact 209).pointIds 209), (.leaf 4 (Common.fact 210).pointIds 210), B0043, (.leaf 6 (Common.fact 211).pointIds 211)]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M7500_7700.SplitData.node0042 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0043
  · rfl

def B0041 : Block := .branch 88 ![288230376151712129, 302231671076439407461890, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0042]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M7500_7700.SplitData.node0041 := by
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
  · exact treeEq0042

def B0040 : Block := .branch 78 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 32688374872659718539012391249872527294528] ![(.leaf 0 (Common.fact 142).pointIds 142), B0041, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 199).pointIds 199)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M7500_7700.SplitData.node0040 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0041
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0039 : Block := .branch 133 ![288230376151712129, 216172782113785346, 6148, 24584, 182688053115506591816447190585133387587640197136, 393248, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M7500_7700.SplitData.node0039 := by
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
  · exact treeEq0040

def B0038 : Block := .branch 157 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 21799339131189687708184403812055944527936] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0039, (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 0 [] 0)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M7500_7700.SplitData.node0038 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · rfl

def B0037 : Block := .branch 114 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 184).pointIds 184), (.leaf 3 (Common.fact 185).pointIds 185), (.leaf 4 (Common.fact 186).pointIds 186), B0038, (.leaf 6 (Common.fact 187).pointIds 187)]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M7500_7700.SplitData.node0037 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0038
  · rfl

def B0036 : Block := .branch 144 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0037, (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M7500_7700.SplitData.node0036 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0037
  · rfl

def B0035 : Block := .branch 87 ![288230376151712129, 216172782113785346, 36893488147419109380, 24584, 348449143727040986586495598010130648629264, 393248, 21804656043172672629171108367762703515712] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B0036]
theorem treeEq0035 : B0035.tree = HexagonCover.NBand.M7500_7700.SplitData.node0035 := by
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
  · exact treeEq0036

def B0034 : Block := .branch 65 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21804656043172672629171108367762703515712] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0035, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0034 : B0034.tree = HexagonCover.NBand.M7500_7700.SplitData.node0034 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0035
  · rfl
  · rfl
  · rfl
  · rfl

def B0033 : Block := .branch 122 ![288230376151712129, 216172782113785346, 6148, 24584, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B0034]
theorem treeEq0033 : B0033.tree = HexagonCover.NBand.M7500_7700.SplitData.node0033 := by
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
  · exact treeEq0034

def B0032 : Block := .branch 138 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0033, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0032 : B0032.tree = HexagonCover.NBand.M7500_7700.SplitData.node0032 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0033
  · rfl
  · rfl

def B0031 : Block := .branch 124 ![288230376151712129, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 172).pointIds 172), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0032]
theorem treeEq0031 : B0031.tree = HexagonCover.NBand.M7500_7700.SplitData.node0031 := by
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
  · exact treeEq0032

def B0030 : Block := .branch 58 ![385, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![B0031, Tip0030_0047, (.leaf 2 (Common.fact 167).pointIds 167), (.leaf 3 (Common.fact 168).pointIds 168), (.leaf 4 (Common.fact 169).pointIds 169), (.leaf 5 (Common.fact 170).pointIds 170), (.leaf 6 (Common.fact 171).pointIds 171)]
theorem treeEq0030 : B0030.tree = HexagonCover.NBand.M7500_7700.SplitData.node0030 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0030 : B0030.accepted = true := by decide +kernel
theorem checked0030 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0030 (maskNeeds ![385, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0030]
  exact B0030.sound accepted0030
#print axioms checked0030

end HexagonCover.NBand.M7500_7700.SplitTree.Run0012
