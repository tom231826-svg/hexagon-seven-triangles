import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0000
import HexagonCover.NBand.M7500_7700.SplitTree.Run0002
import HexagonCover.NBand.M7500_7700.SplitTree.Run0003
import HexagonCover.NBand.M7500_7700.SplitTree.Run0004
import HexagonCover.NBand.M7500_7700.SplitTree.Run0005
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0119_0126 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0126 ![590295810358705652097, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7500_7700.SplitTree.Run0002.checked0126
def Tip0119_0242 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0242 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0002.checked0242
def Tip0119_0261 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0261 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0002.checked0261
def Tip0119_0301 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0301 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0003.checked0301
def Tip0119_0340 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0340 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0003.checked0340
def Tip0119_0381 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0381 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0004.checked0381
def Tip0119_0420 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0420 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0004.checked0420
def Tip0119_0460 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0460 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0005.checked0460
def Tip0119_0499 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0499 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0005.checked0499
def B0125 : Block := .branch 88 ![590295810358705652097, 302232535767567862597122, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), Tip0119_0126]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M7500_7700.SplitData.node0125 := by
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
  · rfl

def B0241 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M7500_7700.SplitData.node0241 := by
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

def B0240 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0241, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M7500_7700.SplitData.node0240 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0241
  · rfl
  · rfl

def B0239 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0240, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M7500_7700.SplitData.node0239 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0240
  · rfl

def B0238 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0239, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M7500_7700.SplitData.node0238 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0239
  · rfl
  · rfl

def B0124 : Block := .branch 78 ![590295810358705652097, 1080863910568920578, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0125, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0238]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M7500_7700.SplitData.node0124 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0125
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238

def B0123 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 11861292468192260659204, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), B0124, Tip0119_0242, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M7500_7700.SplitData.node0123 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0124
  · rfl
  · rfl
  · rfl
  · rfl

def B0122 : Block := .branch 73 ![590295810358705652097, 148654816500245333506, 7138925985322615445508, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), B0123, Tip0119_0261, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M7500_7700.SplitData.node0122 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0123
  · rfl
  · rfl
  · rfl
  · rfl

def B0300 : Block := .branch 73 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0119_0301, Tip0119_0340, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M7500_7700.SplitData.node0300 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0121 : Block := .branch 72 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), B0122, B0300, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M7500_7700.SplitData.node0121 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0122
  · exact treeEq0300
  · rfl
  · rfl
  · rfl

def B0380 : Block := .branch 73 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0119_0381, Tip0119_0420, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M7500_7700.SplitData.node0380 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0459 : Block := .branch 73 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0119_0460, Tip0119_0499, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M7500_7700.SplitData.node0459 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0379 : Block := .branch 72 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), B0380, B0459, (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M7500_7700.SplitData.node0379 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0380
  · exact treeEq0459
  · rfl
  · rfl
  · rfl

def B0120 : Block := .branch 71 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), B0121, B0379, (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M7500_7700.SplitData.node0120 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0121
  · exact treeEq0379
  · rfl
  · rfl
  · rfl

def B0539 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 684).pointIds 684), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0539 : B0539.tree = HexagonCover.NBand.M7500_7700.SplitData.node0539 := by
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

def B0538 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0539, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq0538 : B0538.tree = HexagonCover.NBand.M7500_7700.SplitData.node0538 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0539
  · rfl
  · rfl

def B0119 : Block := .branch 69 ![385, 148654816500245333506, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![B0120, (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 450).pointIds 450), (.leaf 4 (Common.fact 451).pointIds 451), (.leaf 5 (Common.fact 452).pointIds 452), B0538]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M7500_7700.SplitData.node0119 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0120
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0538

theorem accepted0119 : B0119.accepted = true := by decide +kernel
theorem checked0119 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0119 (maskNeeds ![385, 148654816500245333506, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0119]
  exact B0119.sound accepted0119
#print axioms checked0119

def B0564 : Block := .branch 79 ![748288838313443561768219193004703366976801947517313, 216172782113785346, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 465).pointIds 465), (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0564 : B0564.tree = HexagonCover.NBand.M7500_7700.SplitData.node0564 := by
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

def B0563 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![B0564, (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0563 : B0563.tree = HexagonCover.NBand.M7500_7700.SplitData.node0563 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0564
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0562 : Block := .branch 138 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0563, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0562 : B0562.tree = HexagonCover.NBand.M7500_7700.SplitData.node0562 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0563
  · rfl
  · rfl

def B0561 : Block := .branch 139 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), B0562, (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 711).pointIds 711)]
theorem treeEq0561 : B0561.tree = HexagonCover.NBand.M7500_7700.SplitData.node0561 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0562
  · rfl
  · rfl

def B0560 : Block := .branch 140 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0561, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0560 : B0560.tree = HexagonCover.NBand.M7500_7700.SplitData.node0560 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0561
  · rfl
  · rfl

def B0559 : Block := .branch 141 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B0560, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq0559 : B0559.tree = HexagonCover.NBand.M7500_7700.SplitData.node0559 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0560
  · rfl
  · rfl

def B0558 : Block := .branch 142 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0559, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M7500_7700.SplitData.node0558 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0559
  · rfl
  · rfl

def B0557 : Block := .branch 68 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 702).pointIds 702), B0558, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M7500_7700.SplitData.node0557 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0558
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0556 : Block := .branch 165 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182698855038962130087031371948671701637744656400, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 701).pointIds 701), B0557, (.leaf 0 [] 0)]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M7500_7700.SplitData.node0556 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0557
  · rfl

def B0555 : Block := .branch 167 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182698855038962130087031371948671701637744656400, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 700).pointIds 700), B0556, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M7500_7700.SplitData.node0555 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0556
  · rfl

def B0554 : Block := .branch 143 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 565).pointIds 565), (.leaf 1 (Common.fact 566).pointIds 566), (.leaf 2 (Common.fact 567).pointIds 567), (.leaf 3 (Common.fact 568).pointIds 568), B0555, (.leaf 5 (Common.fact 569).pointIds 569), (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M7500_7700.SplitData.node0554 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0555
  · rfl
  · rfl

def B0553 : Block := .branch 129 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), (.leaf 4 (Common.fact 698).pointIds 698), (.leaf 5 (Common.fact 263).pointIds 263), B0554]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M7500_7700.SplitData.node0553 := by
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
  · exact treeEq0554

def B0552 : Block := .branch 130 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), (.leaf 4 (Common.fact 697).pointIds 697), (.leaf 5 (Common.fact 256).pointIds 256), B0553]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M7500_7700.SplitData.node0552 := by
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
  · exact treeEq0553

def B0551 : Block := .branch 131 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 555).pointIds 555), (.leaf 1 (Common.fact 556).pointIds 556), (.leaf 2 (Common.fact 557).pointIds 557), (.leaf 3 (Common.fact 558).pointIds 558), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 560).pointIds 560), B0552]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M7500_7700.SplitData.node0551 := by
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
  · exact treeEq0552

def B0550 : Block := .branch 163 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 185542200051774784537577176028434367729757159440, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 284).pointIds 284), B0551]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M7500_7700.SplitData.node0550 := by
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
  · exact treeEq0551

def B0549 : Block := .branch 151 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0550, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M7500_7700.SplitData.node0549 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0550
  · rfl
  · rfl

def B0548 : Block := .branch 132 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 219).pointIds 219), B0549]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M7500_7700.SplitData.node0548 := by
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
  · exact treeEq0549

def B0547 : Block := .branch 133 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 693).pointIds 693), (.leaf 5 (Common.fact 198).pointIds 198), B0548]
theorem treeEq0547 : B0547.tree = HexagonCover.NBand.M7500_7700.SplitData.node0547 := by
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
  · exact treeEq0548

def B0546 : Block := .branch 157 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 42535295865117307932921825928971419680, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0547, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M7500_7700.SplitData.node0546 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0547
  · rfl
  · rfl

def B0545 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 691).pointIds 691), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0546, (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0545 : B0545.tree = HexagonCover.NBand.M7500_7700.SplitData.node0545 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0546
  · rfl

theorem accepted0545 : B0545.accepted = true := by decide +kernel
theorem checked0545 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0545 (maskNeeds ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424]) := by
  rw [← treeEq0545]
  exact B0545.sound accepted0545
#print axioms checked0545

def Tip0047_0058 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0058 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804666427766544441331276101289724346432] HexagonCover.NBand.M7500_7700.SplitTree.Run0000.checked0058
def Tip0047_0119 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0119 ![385, 148654816500245333506, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] checked0119
def Tip0047_0545 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0545 ![748288838313422294120286634350736906063837462004097, 216172782113785346, 6148, 79228162514264337593543974920, 98320, 393248, 21778071483256974311749925714704515727424] checked0545
def B0057 : Block := .branch 135 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 246).pointIds 246), (.leaf 1 (Common.fact 247).pointIds 247), (.leaf 2 (Common.fact 248).pointIds 248), (.leaf 3 (Common.fact 249).pointIds 249), (.leaf 4 (Common.fact 250).pointIds 250), Tip0047_0058, (.leaf 6 (Common.fact 251).pointIds 251)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M7500_7700.SplitData.node0057 := by
  change Tree.branch (135 : Fin 173) _ = Tree.branch (135 : Fin 173) _
  apply congrArg (Tree.branch (135 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0056 : Block := .branch 140 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0057, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 245).pointIds 245)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M7500_7700.SplitData.node0056 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl

def B0055 : Block := .branch 113 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 239).pointIds 239), (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), B0056]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M7500_7700.SplitData.node0055 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0056

def B0054 : Block := .branch 67 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 233).pointIds 233), B0055, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), (.leaf 6 (Common.fact 238).pointIds 238)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M7500_7700.SplitData.node0054 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0055
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0053 : Block := .branch 144 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804656043172827371676019040297065906240] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0054, (.leaf 6 (Common.fact 181).pointIds 181)]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M7500_7700.SplitData.node0053 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0054
  · rfl

def B0052 : Block := .branch 87 ![576460752303423873, 216172782113785346, 55376261018147624964, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804656043172672629171108367762703515712] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B0053]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M7500_7700.SplitData.node0052 := by
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
  · exact treeEq0053

def B0051 : Block := .branch 65 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804656043172672629171108367762703515712] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0052, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 180).pointIds 180)]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M7500_7700.SplitData.node0051 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0052
  · rfl
  · rfl
  · rfl
  · rfl

def B0050 : Block := .branch 122 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 111).pointIds 111), B0051]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M7500_7700.SplitData.node0050 := by
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
  · exact treeEq0051

def B0049 : Block := .branch 138 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0050, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M7500_7700.SplitData.node0049 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl
  · rfl

def B0048 : Block := .branch 124 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0049]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M7500_7700.SplitData.node0048 := by
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
  · exact treeEq0049

def B0543 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 689).pointIds 689)]
theorem treeEq0543 : B0543.tree = HexagonCover.NBand.M7500_7700.SplitData.node0543 := by
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

def B0542 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0543, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 688).pointIds 688)]
theorem treeEq0542 : B0542.tree = HexagonCover.NBand.M7500_7700.SplitData.node0542 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0543
  · rfl
  · rfl

def B0541 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0542, (.leaf 6 (Common.fact 687).pointIds 687)]
theorem treeEq0541 : B0541.tree = HexagonCover.NBand.M7500_7700.SplitData.node0541 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0542
  · rfl

def B0540 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0541, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq0540 : B0540.tree = HexagonCover.NBand.M7500_7700.SplitData.node0540 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0541
  · rfl
  · rfl

def B0118 : Block := .branch 67 ![385, 1080863910568920578, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 233).pointIds 233), Tip0047_0119, (.leaf 2 (Common.fact 234).pointIds 234), (.leaf 3 (Common.fact 235).pointIds 235), (.leaf 4 (Common.fact 236).pointIds 236), (.leaf 5 (Common.fact 237).pointIds 237), B0540]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M7500_7700.SplitData.node0118 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0540

def B0117 : Block := .branch 87 ![385, 1080863910568920578, 55376261018147624964, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), B0118]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M7500_7700.SplitData.node0117 := by
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
  · exact treeEq0118

def B0544 : Block := .branch 169 ![385, 1080863910568920578, 18482772870728521732, 79266848140492005727134572552, 98320, 393248, 21778071483256974311749925714704515727424] ![Tip0047_0545, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0544 : B0544.tree = HexagonCover.NBand.M7500_7700.SplitData.node0544 := by
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
  · rfl

def B0116 : Block := .branch 65 ![385, 1080863910568920578, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), B0117, (.leaf 3 (Common.fact 114).pointIds 114), (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B0544]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M7500_7700.SplitData.node0116 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0117
  · rfl
  · rfl
  · rfl
  · exact treeEq0544

def B0047 : Block := .branch 59 ![385, 504403158265497090, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192] ![B0048, B0116, (.leaf 2 (Common.fact 227).pointIds 227), (.leaf 3 (Common.fact 228).pointIds 228), (.leaf 4 (Common.fact 229).pointIds 229), (.leaf 5 (Common.fact 230).pointIds 230), (.leaf 6 (Common.fact 231).pointIds 231)]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M7500_7700.SplitData.node0047 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0048
  · exact treeEq0116
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0047 : B0047.accepted = true := by decide +kernel
theorem checked0047 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0047 (maskNeeds ![385, 504403158265497090, 18482772870728521732, 79286190953605839793929871368, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0047]
  exact B0047.sound accepted0047
#print axioms checked0047

def B0659 : Block := .branch 172 ![2244866514940288155201089320241595103445331906396545, 1238544502195328326974834178, 153476982750857507379204, 8769009998209989372742602289545497123000919547912, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 795).pointIds 795), (.leaf 3 (Common.fact 796).pointIds 796), (.leaf 4 (Common.fact 797).pointIds 797), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 799).pointIds 799)]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M7500_7700.SplitData.node0659 := by
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
  · rfl

def B0660 : Block := .branch 172 ![2244866514940288155201089320241595103445331906396545, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699029263533993607524665196470706703068921872, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![(.leaf 0 (Common.fact 793).pointIds 793), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 795).pointIds 795), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 799).pointIds 799)]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M7500_7700.SplitData.node0660 := by
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
  · rfl

def B0658 : Block := .branch 137 ![2244866514940288155201089320241595103445331906396545, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0659, B0660, (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M7500_7700.SplitData.node0658 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · exact treeEq0660
  · rfl
  · rfl

def B0661 : Block := .branch 172 ![2244866514940266887553156761587628642532367420883329, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659810806782918955787790021386338687254592] ![(.leaf 0 (Common.fact 802).pointIds 802), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 795).pointIds 795), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 797).pointIds 797), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M7500_7700.SplitData.node0661 := by
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
  · rfl

def B0657 : Block := .branch 124 ![2244866514940266887553156761587628642532367420883329, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![B0658, (.leaf 1 (Common.fact 173).pointIds 173), (.leaf 2 (Common.fact 174).pointIds 174), (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), B0661]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M7500_7700.SplitData.node0657 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0658
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0661

def B0662 : Block := .branch 172 ![2244866514940266882363395204253257472804864498073985, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 795).pointIds 795), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 797).pointIds 797), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 805).pointIds 805)]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M7500_7700.SplitData.node0662 := by
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
  · rfl

def B0656 : Block := .branch 112 ![2244866514940266882363395204253257472804864498073985, 1238544502195328326974834178, 153476982750857507379204, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![B0657, (.leaf 1 (Common.fact 484).pointIds 484), (.leaf 2 (Common.fact 485).pointIds 485), (.leaf 3 (Common.fact 486).pointIds 486), (.leaf 4 (Common.fact 487).pointIds 487), (.leaf 5 (Common.fact 488).pointIds 488), B0662]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M7500_7700.SplitData.node0656 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0657
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0662

def B0663 : Block := .branch 172 ![2244866514940266882363395204253257472804864498073985, 1238544502195328326974834178, 77992906001238022166532, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 22458636218049744082431591616906169679936] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 806).pointIds 806), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 797).pointIds 797), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M7500_7700.SplitData.node0663 := by
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
  · rfl

def B0655 : Block := .branch 77 ![2244866514940266882363395204253257472804864498073985, 1238846733650231984268510722, 77992906001238022166532, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![(.leaf 0 (Common.fact 352).pointIds 352), (.leaf 1 (Common.fact 792).pointIds 792), B0656, (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), B0663]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M7500_7700.SplitData.node0655 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0656
  · rfl
  · rfl
  · rfl
  · exact treeEq0663

def B0664 : Block := .branch 172 ![2244866514940266882363395204253257472804864498073985, 1238544502195328326974834178, 77919119024943183960068, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 22458636218049589188884740468837998657600] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 794).pointIds 794), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 797).pointIds 797), (.leaf 5 (Common.fact 798).pointIds 798), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M7500_7700.SplitData.node0664 := by
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
  · rfl

def B0654 : Block := .branch 66 ![2244866514940266882363395204253257472804864498073985, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136254047734051789874870904946752] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 791).pointIds 791), B0655, (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), B0664]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M7500_7700.SplitData.node0654 := by
  change Tree.branch (66 : Fin 173) _ = Tree.branch (66 : Fin 173) _
  apply congrArg (Tree.branch (66 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0655
  · rfl
  · rfl
  · rfl
  · exact treeEq0664

def B0653 : Block := .branch 89 ![2244866514940266882363395204253257472804864498073985, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501659789539136253428764032147184733455384640] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 790).pointIds 790), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), (.leaf 4 (Common.fact 74).pointIds 74), (.leaf 5 (Common.fact 75).pointIds 75), B0654]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M7500_7700.SplitData.node0653 := by
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
  · exact treeEq0654

def B0652 : Block := .branch 101 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876143047459761072725367363493896, 182699203488105857128017958444269711768393187344, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![B0653, (.leaf 1 (Common.fact 626).pointIds 626), (.leaf 2 (Common.fact 627).pointIds 627), (.leaf 3 (Common.fact 628).pointIds 628), (.leaf 4 (Common.fact 629).pointIds 629), (.leaf 5 (Common.fact 630).pointIds 630), (.leaf 6 (Common.fact 789).pointIds 789)]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M7500_7700.SplitData.node0652 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0653
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0651 : Block := .branch 138 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0652, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 788).pointIds 788)]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M7500_7700.SplitData.node0651 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0652
  · rfl
  · rfl

def B0650 : Block := .branch 139 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), B0651, (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 787).pointIds 787)]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M7500_7700.SplitData.node0650 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0651
  · rfl
  · rfl

def B0649 : Block := .branch 140 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0650, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 786).pointIds 786)]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M7500_7700.SplitData.node0649 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0650
  · rfl
  · rfl

def B0648 : Block := .branch 141 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), B0649, (.leaf 5 (Common.fact 86).pointIds 86), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M7500_7700.SplitData.node0648 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0649
  · rfl
  · rfl

def B0647 : Block := .branch 142 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3226995615226676178689601227945485829226228026310688, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0648, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M7500_7700.SplitData.node0647 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0648
  · rfl
  · rfl

def B0646 : Block := .branch 165 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 3180227562832087285307083313298564772597238184935456, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 701).pointIds 701), B0647, (.leaf 0 [] 0)]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M7500_7700.SplitData.node0646 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0647
  · rfl

def B0645 : Block := .branch 167 ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305356829503198254015922569280] ![(.leaf 0 (Common.fact 547).pointIds 547), (.leaf 1 (Common.fact 548).pointIds 548), (.leaf 2 (Common.fact 549).pointIds 549), (.leaf 3 (Common.fact 550).pointIds 550), (.leaf 4 (Common.fact 700).pointIds 700), B0646, (.leaf 6 (Common.fact 552).pointIds 552)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M7500_7700.SplitData.node0645 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0646
  · rfl

theorem accepted0645 : B0645.accepted = true := by decide +kernel
theorem checked0645 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0645 (maskNeeds ![2244866514940266882360859903052801014001871091663233, 1238846733650231984268510722, 77919119024943183960068, 8769009824325699876222275622275337062960907444232, 182698855038962130087031371948671701637744656400, 2993155353253731711777011654710880546081278819434528, 1461501665234057007305356829503198254015922569280]) := by
  rw [← treeEq0645]
  exact B0645.sound accepted0645
#print axioms checked0645

end HexagonCover.NBand.M7500_7700.SplitTree.Run0006
