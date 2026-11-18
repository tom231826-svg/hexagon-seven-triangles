import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0001
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0002
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0121_0130 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0130 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182869246670244653129472168296098655524876288016, 42535295865117307932921825928971419680, 21804656043173136856685840385365790687296] HexagonCover.NBand.M7700_7900.SplitTree.Run0001.checked0130
def Tip0121_0206 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0206 ![10387129018270111715863986064851329, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 185720606013363029522709461774615554621805002768, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] HexagonCover.NBand.M7700_7900.SplitTree.Run0001.checked0206
def B0129 : Block := .branch 138 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182868898221100926088485581800500645394227757072, 42535295865117307932921825928971419680, 21804656043173136856685840385365790687296] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), Tip0121_0130, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 479).pointIds 479)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M7700_7900.SplitData.node0129 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0128 : Block := .branch 141 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182866110627951109760592889835716564349039509520, 42535295865117307932921825928971419680, 21804656043173136856685840385365790687296] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0129, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 478).pointIds 478)]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M7700_7900.SplitData.node0128 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129
  · rfl
  · rfl

def B0127 : Block := .branch 124 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 182866110627951109760592889835716564349039509520, 42535295865117307932921825928971419680, 21783388395240578202719379472401305174080] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), B0128]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M7700_7900.SplitData.node0127 := by
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
  · exact treeEq0128

def B0126 : Block := .branch 122 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 184293358320657069641651175805166059485422256144, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 472).pointIds 472), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), B0127]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M7700_7900.SplitData.node0126 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0127

def B0125 : Block := .branch 157 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0126, (.leaf 5 (Common.fact 470).pointIds 470), (.leaf 0 [] 0)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M7700_7900.SplitData.node0125 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0126
  · rfl
  · rfl

def B0124 : Block := .branch 125 ![604462909807314587353473, 302232391652379786741250, 77946771197023982983172, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 465).pointIds 465), (.leaf 2 (Common.fact 466).pointIds 466), (.leaf 3 (Common.fact 467).pointIds 467), (.leaf 4 (Common.fact 468).pointIds 468), B0125, (.leaf 6 (Common.fact 469).pointIds 469)]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M7700_7900.SplitData.node0124 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0125
  · rfl

def B0199 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq0199 : B0199.tree = HexagonCover.NBand.M7700_7900.SplitData.node0199 := by
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

def B0198 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0199, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 601).pointIds 601)]
theorem treeEq0198 : B0198.tree = HexagonCover.NBand.M7700_7900.SplitData.node0198 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0199
  · rfl
  · rfl

def B0197 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129658680852706406046367808] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0198, (.leaf 6 (Common.fact 600).pointIds 600)]
theorem treeEq0197 : B0197.tree = HexagonCover.NBand.M7700_7900.SplitData.node0197 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0198
  · rfl

def B0123 : Block := .branch 79 ![385, 302232535767567862597122, 77946771197023982983172, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257438539227764244160183795776] ![B0124, (.leaf 1 (Common.fact 209).pointIds 209), (.leaf 2 (Common.fact 210).pointIds 210), (.leaf 3 (Common.fact 211).pointIds 211), (.leaf 4 (Common.fact 212).pointIds 212), (.leaf 5 (Common.fact 213).pointIds 213), B0197]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M7700_7900.SplitData.node0123 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0124
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0197

def B0205 : Block := .branch 151 ![10387129018270111715863986064851329, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 182866110627951109760592889835716564349039509520, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), Tip0121_0206, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 612).pointIds 612)]
theorem treeEq0205 : B0205.tree = HexagonCover.NBand.M7700_7900.SplitData.node0205 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0204 : Block := .branch 101 ![10384593717069655257060992658440577, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 182866110627951109760592889835716564349039509520, 42535295865117307932921825928971419680, 21783388395240114050762511180712541421632] ![B0205, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 611).pointIds 611)]
theorem treeEq0204 : B0204.tree = HexagonCover.NBand.M7700_7900.SplitData.node0204 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0205
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0203 : Block := .branch 122 ![10384593717069655257060992658440577, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 184293358320657069641651175805166059485422256144, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 472).pointIds 472), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), B0204]
theorem treeEq0203 : B0203.tree = HexagonCover.NBand.M7700_7900.SplitData.node0203 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0204

def B0202 : Block := .branch 157 ![10384593717069655257060992658440577, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 42535295865117307932921825928971419680, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0203, (.leaf 5 (Common.fact 470).pointIds 470), (.leaf 0 [] 0)]
theorem treeEq0202 : B0202.tree = HexagonCover.NBand.M7700_7900.SplitData.node0202 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0203
  · rfl
  · rfl

def B0201 : Block := .branch 125 ![10384593717070245552871351364092289, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 465).pointIds 465), (.leaf 2 (Common.fact 466).pointIds 466), (.leaf 3 (Common.fact 467).pointIds 467), (.leaf 4 (Common.fact 468).pointIds 468), B0202, (.leaf 6 (Common.fact 469).pointIds 469)]
theorem treeEq0201 : B0201.tree = HexagonCover.NBand.M7700_7900.SplitData.node0201 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0202
  · rfl

def B0200 : Block := .branch 113 ![590295810358705652097, 302232535767567862597122, 2425782874489825007620, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257438614785627970074507214912] ![B0201, (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), (.leaf 6 (Common.fact 604).pointIds 604)]
theorem treeEq0200 : B0200.tree = HexagonCover.NBand.M7700_7900.SplitData.node0200 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0201
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0122 : Block := .branch 76 ![590295810358705652097, 302232535767567862597122, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B0123, (.leaf 3 (Common.fact 324).pointIds 324), (.leaf 4 (Common.fact 325).pointIds 325), (.leaf 5 (Common.fact 326).pointIds 326), B0200]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M7700_7900.SplitData.node0122 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0123
  · rfl
  · rfl
  · rfl
  · exact treeEq0200

def B0121 : Block := .branch 88 ![590295810358705652097, 302232535767567862597122, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0122]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M7700_7900.SplitData.node0121 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0122

theorem accepted0121 : B0121.accepted = true := by decide +kernel
theorem checked0121 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0121 (maskNeeds ![590295810358705652097, 302232535767567862597122, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0121]
  exact B0121.sound accepted0121
#print axioms checked0121

def B0247 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0247 : B0247.tree = HexagonCover.NBand.M7700_7900.SplitData.node0247 := by
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

def B0246 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0247, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0246 : B0246.tree = HexagonCover.NBand.M7700_7900.SplitData.node0246 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0247
  · rfl
  · rfl

def B0245 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0246, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0245 : B0245.tree = HexagonCover.NBand.M7700_7900.SplitData.node0245 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0246
  · rfl

def B0244 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0245]
theorem treeEq0244 : B0244.tree = HexagonCover.NBand.M7700_7900.SplitData.node0244 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0245

def B0243 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 38695070960633872881049608, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0244, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 655).pointIds 655), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0243 : B0243.tree = HexagonCover.NBand.M7700_7900.SplitData.node0243 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0244
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0242 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 7138925985322615445508, 38695070960633872881049608, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0243]
theorem treeEq0242 : B0242.tree = HexagonCover.NBand.M7700_7900.SplitData.node0242 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0243

def B0251 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0251 : B0251.tree = HexagonCover.NBand.M7700_7900.SplitData.node0251 := by
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

def B0250 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0251, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0250 : B0250.tree = HexagonCover.NBand.M7700_7900.SplitData.node0250 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0251
  · rfl
  · rfl

def B0249 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0250]
theorem treeEq0249 : B0249.tree = HexagonCover.NBand.M7700_7900.SplitData.node0249 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0250

def B0248 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0249, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 655).pointIds 655), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0248 : B0248.tree = HexagonCover.NBand.M7700_7900.SplitData.node0248 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0249
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0241 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0242, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0248]
theorem treeEq0241 : B0241.tree = HexagonCover.NBand.M7700_7900.SplitData.node0241 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0242
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0248

theorem accepted0241 : B0241.accepted = true := by decide +kernel
theorem checked0241 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0241 (maskNeeds ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0241]
  exact B0241.sound accepted0241
#print axioms checked0241

def Tip0119_0121 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0121 ![590295810358705652097, 302232535767567862597122, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129054217942899091459014720] checked0121
def B0228 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0228 : B0228.tree = HexagonCover.NBand.M7700_7900.SplitData.node0228 := by
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

def B0227 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0228, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq0227 : B0227.tree = HexagonCover.NBand.M7700_7900.SplitData.node0227 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0228
  · rfl
  · rfl

def B0226 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0227, (.leaf 6 (Common.fact 637).pointIds 637)]
theorem treeEq0226 : B0226.tree = HexagonCover.NBand.M7700_7900.SplitData.node0226 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0227
  · rfl

def B0120 : Block := .branch 78 ![590295810358705652097, 1080863910568920578, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), Tip0119_0121, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0226]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M7700_7900.SplitData.node0120 := by
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
  · exact treeEq0226

def B0235 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0235 : B0235.tree = HexagonCover.NBand.M7700_7900.SplitData.node0235 := by
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

def B0234 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0235, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0234 : B0234.tree = HexagonCover.NBand.M7700_7900.SplitData.node0234 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0235
  · rfl
  · rfl

def B0233 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0234, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0233 : B0233.tree = HexagonCover.NBand.M7700_7900.SplitData.node0233 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0234
  · rfl

def B0232 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0233]
theorem treeEq0232 : B0232.tree = HexagonCover.NBand.M7700_7900.SplitData.node0232 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0233

def B0231 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 11861292468192260659204, 38704515693599612171477000, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0232, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 642).pointIds 642), (.leaf 3 (Common.fact 643).pointIds 643), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0231 : B0231.tree = HexagonCover.NBand.M7700_7900.SplitData.node0231 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0232
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0230 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 11861292468192260659204, 38704515693599612171477000, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0231]
theorem treeEq0230 : B0230.tree = HexagonCover.NBand.M7700_7900.SplitData.node0230 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0231

def B0239 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0239 : B0239.tree = HexagonCover.NBand.M7700_7900.SplitData.node0239 := by
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

def B0238 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0239, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0238 : B0238.tree = HexagonCover.NBand.M7700_7900.SplitData.node0238 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0239
  · rfl
  · rfl

def B0237 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0238]
theorem treeEq0237 : B0237.tree = HexagonCover.NBand.M7700_7900.SplitData.node0237 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0238

def B0236 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 11861292468192260659204, 79266867029957937205715427336, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0237, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 642).pointIds 642), (.leaf 3 (Common.fact 643).pointIds 643), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0236 : B0236.tree = HexagonCover.NBand.M7700_7900.SplitData.node0236 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0237
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0229 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 11861292468192260659204, 79266867029957937205715427336, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0230, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0236]
theorem treeEq0229 : B0229.tree = HexagonCover.NBand.M7700_7900.SplitData.node0229 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0230
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0236

def B0119 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 11870533924996369094660, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), B0120, B0229, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M7700_7900.SplitData.node0119 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0120
  · exact treeEq0229
  · rfl
  · rfl
  · rfl

theorem accepted0119 : B0119.accepted = true := by decide +kernel
theorem checked0119 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0119 (maskNeeds ![590295810358705652097, 148654816500245333506, 11870533924996369094660, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0119]
  exact B0119.sound accepted0119
#print axioms checked0119

def B0271 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0271 : B0271.tree = HexagonCover.NBand.M7700_7900.SplitData.node0271 := by
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

def B0270 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0271, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0270 : B0270.tree = HexagonCover.NBand.M7700_7900.SplitData.node0270 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0271
  · rfl
  · rfl

def B0269 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0270, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0269 : B0269.tree = HexagonCover.NBand.M7700_7900.SplitData.node0269 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0270
  · rfl

def B0268 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0269]
theorem treeEq0268 : B0268.tree = HexagonCover.NBand.M7700_7900.SplitData.node0268 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0269

def B0267 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0268, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0267 : B0267.tree = HexagonCover.NBand.M7700_7900.SplitData.node0267 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0268
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0266 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0267]
theorem treeEq0266 : B0266.tree = HexagonCover.NBand.M7700_7900.SplitData.node0266 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0267

def B0275 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0275 : B0275.tree = HexagonCover.NBand.M7700_7900.SplitData.node0275 := by
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

def B0274 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0275, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0274 : B0274.tree = HexagonCover.NBand.M7700_7900.SplitData.node0274 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0275
  · rfl
  · rfl

def B0273 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0274]
theorem treeEq0273 : B0273.tree = HexagonCover.NBand.M7700_7900.SplitData.node0273 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0274

def B0272 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0273, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0272 : B0272.tree = HexagonCover.NBand.M7700_7900.SplitData.node0272 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0273
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0265 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0266, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0272]
theorem treeEq0265 : B0265.tree = HexagonCover.NBand.M7700_7900.SplitData.node0265 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0266
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0272

theorem accepted0265 : B0265.accepted = true := by decide +kernel
theorem checked0265 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0265 (maskNeeds ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0265]
  exact B0265.sound accepted0265
#print axioms checked0265

def B0294 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0294 : B0294.tree = HexagonCover.NBand.M7700_7900.SplitData.node0294 := by
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

def B0293 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0294, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0293 : B0293.tree = HexagonCover.NBand.M7700_7900.SplitData.node0293 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0294
  · rfl
  · rfl

def B0292 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0293, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0292 : B0292.tree = HexagonCover.NBand.M7700_7900.SplitData.node0292 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0293
  · rfl

def B0291 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0292]
theorem treeEq0291 : B0291.tree = HexagonCover.NBand.M7700_7900.SplitData.node0291 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0292

def B0290 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0291, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0290 : B0290.tree = HexagonCover.NBand.M7700_7900.SplitData.node0290 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0291
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0289 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0290]
theorem treeEq0289 : B0289.tree = HexagonCover.NBand.M7700_7900.SplitData.node0289 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0290

def B0298 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0298 : B0298.tree = HexagonCover.NBand.M7700_7900.SplitData.node0298 := by
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

def B0297 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0298, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0297 : B0297.tree = HexagonCover.NBand.M7700_7900.SplitData.node0297 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0298
  · rfl
  · rfl

def B0296 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0297]
theorem treeEq0296 : B0296.tree = HexagonCover.NBand.M7700_7900.SplitData.node0296 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0297

def B0295 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0296, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0295 : B0295.tree = HexagonCover.NBand.M7700_7900.SplitData.node0295 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0296
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0288 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0289, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0295]
theorem treeEq0288 : B0288.tree = HexagonCover.NBand.M7700_7900.SplitData.node0288 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0289
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0295

theorem accepted0288 : B0288.accepted = true := by decide +kernel
theorem checked0288 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0288 (maskNeeds ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0288]
  exact B0288.sound accepted0288
#print axioms checked0288

def Tip0264_0265 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0265 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0265
def B0282 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0282 : B0282.tree = HexagonCover.NBand.M7700_7900.SplitData.node0282 := by
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

def B0281 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0282, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0281 : B0281.tree = HexagonCover.NBand.M7700_7900.SplitData.node0281 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0282
  · rfl
  · rfl

def B0280 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0281, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0280 : B0280.tree = HexagonCover.NBand.M7700_7900.SplitData.node0280 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0281
  · rfl

def B0279 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0280]
theorem treeEq0279 : B0279.tree = HexagonCover.NBand.M7700_7900.SplitData.node0279 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0280

def B0278 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0279, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0278 : B0278.tree = HexagonCover.NBand.M7700_7900.SplitData.node0278 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0279
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0277 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0278]
theorem treeEq0277 : B0277.tree = HexagonCover.NBand.M7700_7900.SplitData.node0277 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0278

def B0286 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0286 : B0286.tree = HexagonCover.NBand.M7700_7900.SplitData.node0286 := by
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

def B0285 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0286, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0285 : B0285.tree = HexagonCover.NBand.M7700_7900.SplitData.node0285 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0286
  · rfl
  · rfl

def B0284 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0285]
theorem treeEq0284 : B0284.tree = HexagonCover.NBand.M7700_7900.SplitData.node0284 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0285

def B0283 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0284, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0283 : B0283.tree = HexagonCover.NBand.M7700_7900.SplitData.node0283 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0284
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0276 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0277, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0283]
theorem treeEq0276 : B0276.tree = HexagonCover.NBand.M7700_7900.SplitData.node0276 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0277
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0283

def B0264 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0264_0265, B0276, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0264 : B0264.tree = HexagonCover.NBand.M7700_7900.SplitData.node0264 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0276
  · rfl
  · rfl
  · rfl

theorem accepted0264 : B0264.accepted = true := by decide +kernel
theorem checked0264 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0264 (maskNeeds ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0264]
  exact B0264.sound accepted0264
#print axioms checked0264

end HexagonCover.NBand.M7700_7900.SplitTree.Run0002
