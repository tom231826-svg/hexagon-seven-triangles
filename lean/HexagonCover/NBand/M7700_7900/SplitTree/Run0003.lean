import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0002
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0118_0241 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0241 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0002.checked0241
def Tip0118_0119 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0119 ![590295810358705652097, 148654816500245333506, 11870533924996369094660, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0002.checked0119
def B0258 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0258 : B0258.tree = HexagonCover.NBand.M7700_7900.SplitData.node0258 := by
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

def B0257 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0258, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0257 : B0257.tree = HexagonCover.NBand.M7700_7900.SplitData.node0257 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0258
  · rfl
  · rfl

def B0256 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0257, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0256 : B0256.tree = HexagonCover.NBand.M7700_7900.SplitData.node0256 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0257
  · rfl

def B0255 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0256]
theorem treeEq0255 : B0255.tree = HexagonCover.NBand.M7700_7900.SplitData.node0255 := by
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
  · exact treeEq0256

def B0254 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 38695070960633872881049608, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0255, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 655).pointIds 655), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0254 : B0254.tree = HexagonCover.NBand.M7700_7900.SplitData.node0254 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0255
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0253 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 7138925985322615445508, 38695070960633872881049608, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0254]
theorem treeEq0253 : B0253.tree = HexagonCover.NBand.M7700_7900.SplitData.node0253 := by
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
  · exact treeEq0254

def B0262 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0262 : B0262.tree = HexagonCover.NBand.M7700_7900.SplitData.node0262 := by
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

def B0261 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0262, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0261 : B0261.tree = HexagonCover.NBand.M7700_7900.SplitData.node0261 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0262
  · rfl
  · rfl

def B0260 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0261]
theorem treeEq0260 : B0260.tree = HexagonCover.NBand.M7700_7900.SplitData.node0260 := by
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
  · exact treeEq0261

def B0259 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0260, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 655).pointIds 655), (.leaf 3 (Common.fact 656).pointIds 656), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0259 : B0259.tree = HexagonCover.NBand.M7700_7900.SplitData.node0259 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0260
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0252 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0253, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0259]
theorem treeEq0252 : B0252.tree = HexagonCover.NBand.M7700_7900.SplitData.node0252 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0253
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0259

def B0240 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 7138925985322615445508, 79266857585224971466424999944, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0118_0241, B0252, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0240 : B0240.tree = HexagonCover.NBand.M7700_7900.SplitData.node0240 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0252
  · rfl
  · rfl
  · rfl

def B0118 : Block := .branch 73 ![590295810358705652097, 148654816500245333506, 7148167442126723880964, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), Tip0118_0119, B0240, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M7700_7900.SplitData.node0118 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0240
  · rfl
  · rfl
  · rfl

theorem accepted0118 : B0118.accepted = true := by decide +kernel
theorem checked0118 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0118 (maskNeeds ![590295810358705652097, 148654816500245333506, 7148167442126723880964, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0118]
  exact B0118.sound accepted0118
#print axioms checked0118

def B0319 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M7700_7900.SplitData.node0319 := by
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

def B0318 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0319, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M7700_7900.SplitData.node0318 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0319
  · rfl
  · rfl

def B0317 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0318, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M7700_7900.SplitData.node0317 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0318
  · rfl

def B0316 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0317]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M7700_7900.SplitData.node0316 := by
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
  · exact treeEq0317

def B0315 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0316, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M7700_7900.SplitData.node0315 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0316
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0314 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0315]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M7700_7900.SplitData.node0314 := by
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
  · exact treeEq0315

def B0323 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M7700_7900.SplitData.node0323 := by
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

def B0322 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0323, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M7700_7900.SplitData.node0322 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0323
  · rfl
  · rfl

def B0321 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0322]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M7700_7900.SplitData.node0321 := by
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
  · exact treeEq0322

def B0320 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0321, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M7700_7900.SplitData.node0320 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0321
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0313 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0314, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0320]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M7700_7900.SplitData.node0313 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0314
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0320

theorem accepted0313 : B0313.accepted = true := by decide +kernel
theorem checked0313 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0313 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0313]
  exact B0313.sound accepted0313
#print axioms checked0313

def B0342 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M7700_7900.SplitData.node0342 := by
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

def B0341 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0342, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M7700_7900.SplitData.node0341 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0342
  · rfl
  · rfl

def B0340 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0341, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M7700_7900.SplitData.node0340 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0341
  · rfl

def B0339 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0340]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M7700_7900.SplitData.node0339 := by
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
  · exact treeEq0340

def B0338 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0339, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M7700_7900.SplitData.node0338 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0339
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0337 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0338]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M7700_7900.SplitData.node0337 := by
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
  · exact treeEq0338

def B0346 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M7700_7900.SplitData.node0346 := by
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

def B0345 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0346, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M7700_7900.SplitData.node0345 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0346
  · rfl
  · rfl

def B0344 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0345]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M7700_7900.SplitData.node0344 := by
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
  · exact treeEq0345

def B0343 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0344, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M7700_7900.SplitData.node0343 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0344
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0336 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0337, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0343]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M7700_7900.SplitData.node0336 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0337
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0343

theorem accepted0336 : B0336.accepted = true := by decide +kernel
theorem checked0336 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0336 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0336]
  exact B0336.sound accepted0336
#print axioms checked0336

def Tip0312_0313 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0313 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0313
def B0330 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M7700_7900.SplitData.node0330 := by
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

def B0329 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0330, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M7700_7900.SplitData.node0329 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0330
  · rfl
  · rfl

def B0328 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0329, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M7700_7900.SplitData.node0328 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0329
  · rfl

def B0327 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0328]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M7700_7900.SplitData.node0327 := by
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
  · exact treeEq0328

def B0326 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0327, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M7700_7900.SplitData.node0326 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0327
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0325 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0326]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M7700_7900.SplitData.node0325 := by
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
  · exact treeEq0326

def B0334 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M7700_7900.SplitData.node0334 := by
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

def B0333 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0334, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M7700_7900.SplitData.node0333 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl
  · rfl

def B0332 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0333]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M7700_7900.SplitData.node0332 := by
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
  · exact treeEq0333

def B0331 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0332, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M7700_7900.SplitData.node0331 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0332
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0324 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0325, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0331]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M7700_7900.SplitData.node0324 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0325
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0331

def B0312 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0312_0313, B0324, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M7700_7900.SplitData.node0312 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · rfl
  · rfl

theorem accepted0312 : B0312.accepted = true := by decide +kernel
theorem checked0312 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0312 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0312]
  exact B0312.sound accepted0312
#print axioms checked0312

def B0366 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M7700_7900.SplitData.node0366 := by
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

def B0365 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0366, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M7700_7900.SplitData.node0365 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0366
  · rfl
  · rfl

def B0364 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0365, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M7700_7900.SplitData.node0364 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl

def B0363 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0364]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M7700_7900.SplitData.node0363 := by
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
  · exact treeEq0364

def B0362 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0363, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M7700_7900.SplitData.node0362 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0363
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0361 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0362]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M7700_7900.SplitData.node0361 := by
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
  · exact treeEq0362

def B0370 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M7700_7900.SplitData.node0370 := by
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

def B0369 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0370, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M7700_7900.SplitData.node0369 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0370
  · rfl
  · rfl

def B0368 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0369]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M7700_7900.SplitData.node0368 := by
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
  · exact treeEq0369

def B0367 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0368, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M7700_7900.SplitData.node0367 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0360 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0361, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0367]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M7700_7900.SplitData.node0360 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0361
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0367

theorem accepted0360 : B0360.accepted = true := by decide +kernel
theorem checked0360 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0360 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0360]
  exact B0360.sound accepted0360
#print axioms checked0360

def B0389 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M7700_7900.SplitData.node0389 := by
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

def B0388 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0389, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M7700_7900.SplitData.node0388 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0389
  · rfl
  · rfl

def B0387 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0388, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M7700_7900.SplitData.node0387 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0388
  · rfl

def B0386 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0387]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M7700_7900.SplitData.node0386 := by
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
  · exact treeEq0387

def B0385 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0386, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M7700_7900.SplitData.node0385 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0386
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0384 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0385]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M7700_7900.SplitData.node0384 := by
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
  · exact treeEq0385

def B0393 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M7700_7900.SplitData.node0393 := by
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

def B0392 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0393, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M7700_7900.SplitData.node0392 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0393
  · rfl
  · rfl

def B0391 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0392]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M7700_7900.SplitData.node0391 := by
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
  · exact treeEq0392

def B0390 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0391, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M7700_7900.SplitData.node0390 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0391
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0383 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0384, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0390]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M7700_7900.SplitData.node0383 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0384
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0390

theorem accepted0383 : B0383.accepted = true := by decide +kernel
theorem checked0383 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0383 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0383]
  exact B0383.sound accepted0383
#print axioms checked0383

end HexagonCover.NBand.M7700_7900.SplitTree.Run0003
