import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0000
import HexagonCover.NBand.M7700_7900.SplitTree.Run0002
import HexagonCover.NBand.M7700_7900.SplitTree.Run0003
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0359_0360 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0360 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0003.checked0360
def B0377 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M7700_7900.SplitData.node0377 := by
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

def B0376 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0377, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M7700_7900.SplitData.node0376 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl
  · rfl

def B0375 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0376, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M7700_7900.SplitData.node0375 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0376
  · rfl

def B0374 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0375]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M7700_7900.SplitData.node0374 := by
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
  · exact treeEq0375

def B0373 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0374, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M7700_7900.SplitData.node0373 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0374
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0372 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0373]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M7700_7900.SplitData.node0372 := by
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
  · exact treeEq0373

def B0381 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M7700_7900.SplitData.node0381 := by
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

def B0380 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0381, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M7700_7900.SplitData.node0380 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0381
  · rfl
  · rfl

def B0379 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0380]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M7700_7900.SplitData.node0379 := by
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
  · exact treeEq0380

def B0378 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0379, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M7700_7900.SplitData.node0378 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0379
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0371 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0372, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0378]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M7700_7900.SplitData.node0371 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0372
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0378

def B0359 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0359_0360, B0371, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M7700_7900.SplitData.node0359 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0371
  · rfl
  · rfl
  · rfl

theorem accepted0359 : B0359.accepted = true := by decide +kernel
theorem checked0359 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0359 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0359]
  exact B0359.sound accepted0359
#print axioms checked0359

def Tip0311_0336 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0336 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0003.checked0336
def Tip0311_0312 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0312 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0003.checked0312
def B0353 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M7700_7900.SplitData.node0353 := by
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

def B0352 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0353, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M7700_7900.SplitData.node0352 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0353
  · rfl
  · rfl

def B0351 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0352, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M7700_7900.SplitData.node0351 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl

def B0350 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0351]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M7700_7900.SplitData.node0350 := by
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
  · exact treeEq0351

def B0349 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0350, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M7700_7900.SplitData.node0349 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0348 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0349]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M7700_7900.SplitData.node0348 := by
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
  · exact treeEq0349

def B0357 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M7700_7900.SplitData.node0357 := by
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

def B0356 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0357, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M7700_7900.SplitData.node0356 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0357
  · rfl
  · rfl

def B0355 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0356]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M7700_7900.SplitData.node0355 := by
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
  · exact treeEq0356

def B0354 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0355, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M7700_7900.SplitData.node0354 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0347 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0348, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0354]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M7700_7900.SplitData.node0347 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0348
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0354

def B0335 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0311_0336, B0347, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M7700_7900.SplitData.node0335 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0347
  · rfl
  · rfl
  · rfl

def B0311 : Block := .branch 73 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), Tip0311_0312, B0335, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M7700_7900.SplitData.node0311 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0335
  · rfl
  · rfl
  · rfl

theorem accepted0311 : B0311.accepted = true := by decide +kernel
theorem checked0311 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0311 (maskNeeds ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0311]
  exact B0311.sound accepted0311
#print axioms checked0311

def Tip0117_0288 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0288 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0002.checked0288
def Tip0117_0264 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0264 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0002.checked0264
def Tip0117_0118 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0118 ![590295810358705652097, 148654816500245333506, 7148167442126723880964, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0003.checked0118
def B0305 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M7700_7900.SplitData.node0305 := by
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

def B0304 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0305, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M7700_7900.SplitData.node0304 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0305
  · rfl
  · rfl

def B0303 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0304, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M7700_7900.SplitData.node0303 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0304
  · rfl

def B0302 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0303]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M7700_7900.SplitData.node0302 := by
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
  · exact treeEq0303

def B0301 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0302, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M7700_7900.SplitData.node0301 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0302
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0300 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 2416559502452970231812, 38690348594151003235835912, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0301]
theorem treeEq0300 : B0300.tree = HexagonCover.NBand.M7700_7900.SplitData.node0300 := by
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
  · exact treeEq0301

def B0309 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M7700_7900.SplitData.node0309 := by
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

def B0308 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0309, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M7700_7900.SplitData.node0308 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0309
  · rfl
  · rfl

def B0307 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0308]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M7700_7900.SplitData.node0307 := by
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
  · exact treeEq0308

def B0306 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0307, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 657).pointIds 657), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M7700_7900.SplitData.node0306 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0307
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0299 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0300, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0306]
theorem treeEq0299 : B0299.tree = HexagonCover.NBand.M7700_7900.SplitData.node0299 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0300
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0306

def B0287 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0117_0288, B0299, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0287 : B0287.tree = HexagonCover.NBand.M7700_7900.SplitData.node0287 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0299
  · rfl
  · rfl
  · rfl

def B0263 : Block := .branch 73 ![590295810358705652097, 148510701312169477634, 2416559502452970231812, 79266852862858488596779786248, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), Tip0117_0264, B0287, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0263 : B0263.tree = HexagonCover.NBand.M7700_7900.SplitData.node0263 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0287
  · rfl
  · rfl
  · rfl

def B0117 : Block := .branch 72 ![590295810358705652097, 148654816500245333506, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), Tip0117_0118, B0263, (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M7700_7900.SplitData.node0117 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0263
  · rfl
  · rfl
  · rfl

theorem accepted0117 : B0117.accepted = true := by decide +kernel
theorem checked0117 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0117 (maskNeeds ![590295810358705652097, 148654816500245333506, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0117]
  exact B0117.sound accepted0117
#print axioms checked0117

def Tip0115_0383 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0383 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0003.checked0383
def Tip0115_0359 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0359 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0359
def Tip0115_0311 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0311 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0311
def Tip0115_0117 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0117 ![590295810358705652097, 148654816500245333506, 2425800959257078667268, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0117
def B0400 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 602).pointIds 602), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 650).pointIds 650)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M7700_7900.SplitData.node0400 := by
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

def B0399 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0400, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M7700_7900.SplitData.node0399 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0400
  · rfl
  · rfl

def B0398 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 748288838335200365603543763404954848962928921018432] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0399, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M7700_7900.SplitData.node0398 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0399
  · rfl

def B0397 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0398]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M7700_7900.SplitData.node0397 := by
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
  · exact treeEq0398

def B0396 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0397, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M7700_7900.SplitData.node0396 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0397
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0395 : Block := .branch 88 ![590295810358705652097, 302379965604969463154178, 55376261018147624964, 38687987410909568413229064, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0396]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M7700_7900.SplitData.node0395 := by
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
  · exact treeEq0396

def B0404 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M7700_7900.SplitData.node0404 := by
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

def B0403 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 748288838335200365603543763707186303866586214694976] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0404, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M7700_7900.SplitData.node0403 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0404
  · rfl
  · rfl

def B0402 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 936748722493064706, 18482772870728521732, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 647).pointIds 647), (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), B0403]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M7700_7900.SplitData.node0402 := by
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
  · exact treeEq0403

def B0401 : Block := .branch 170 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0402, (.leaf 1 (Common.fact 641).pointIds 641), (.leaf 2 (Common.fact 659).pointIds 659), (.leaf 3 (Common.fact 660).pointIds 660), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M7700_7900.SplitData.node0401 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0402
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0394 : Block := .branch 78 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0395, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0401]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M7700_7900.SplitData.node0394 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0395
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0401

def B0382 : Block := .branch 74 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0115_0383, B0394, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M7700_7900.SplitData.node0382 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0394
  · rfl
  · rfl
  · rfl

def B0358 : Block := .branch 73 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), Tip0115_0359, B0382, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M7700_7900.SplitData.node0358 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0382
  · rfl
  · rfl
  · rfl

def B0310 : Block := .branch 72 ![590295810358705652097, 148510701312169477634, 55376261018147624964, 79266850501675247161957179400, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), Tip0115_0311, B0358, (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M7700_7900.SplitData.node0310 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0358
  · rfl
  · rfl
  · rfl

def B0116 : Block := .branch 71 ![590295810358705652097, 148654816500245333506, 64617717822256060420, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), Tip0115_0117, B0310, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M7700_7900.SplitData.node0116 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0310
  · rfl
  · rfl
  · rfl

def B0406 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M7700_7900.SplitData.node0406 := by
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

def B0405 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0406, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M7700_7900.SplitData.node0405 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0406
  · rfl
  · rfl

def B0115 : Block := .branch 69 ![385, 148654816500245333506, 64617717822256060420, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0116, (.leaf 1 (Common.fact 459).pointIds 459), (.leaf 2 (Common.fact 460).pointIds 460), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 462).pointIds 462), (.leaf 5 (Common.fact 463).pointIds 463), B0405]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M7700_7900.SplitData.node0115 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0116
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0405

theorem accepted0115 : B0115.accepted = true := by decide +kernel
theorem checked0115 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0115 (maskNeeds ![385, 148654816500245333506, 64617717822256060420, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0115]
  exact B0115.sound accepted0115
#print axioms checked0115

def Tip0040_0052 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0052 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688054476636059500201044438631817314713042960, 393248, 11188505502393299867049435867681419867717696] HexagonCover.NBand.M7700_7900.SplitTree.Run0000.checked0052
def B0051 : Block := .branch 143 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688054476636059500201044438631817314713042960, 393248, 38132903127988296281576731357239114727488] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), (.leaf 4 (Common.fact 233).pointIds 233), (.leaf 5 (Common.fact 234).pointIds 234), Tip0040_0052]
theorem treeEq0051 : B0051.tree = HexagonCover.NBand.M7700_7900.SplitData.node0051 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0050 : Block := .branch 130 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 393248, 38132903127988296281576731357239114727488] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), B0051, (.leaf 5 (Common.fact 227).pointIds 227), (.leaf 6 (Common.fact 228).pointIds 228)]
theorem treeEq0050 : B0050.tree = HexagonCover.NBand.M7700_7900.SplitData.node0050 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · rfl

def B0049 : Block := .branch 79 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 393248, 38132903127988296281576731357239114727488] ![B0050, (.leaf 1 (Common.fact 209).pointIds 209), (.leaf 2 (Common.fact 210).pointIds 210), (.leaf 3 (Common.fact 211).pointIds 211), (.leaf 4 (Common.fact 212).pointIds 212), (.leaf 5 (Common.fact 213).pointIds 213), (.leaf 6 (Common.fact 214).pointIds 214)]
theorem treeEq0049 : B0049.tree = HexagonCover.NBand.M7700_7900.SplitData.node0049 := by
  change Tree.branch (79 : Fin 172) _ = Tree.branch (79 : Fin 172) _
  apply congrArg (Tree.branch (79 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0050
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0048 : Block := .branch 132 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 182689446912081499980393536567525428110234320912, 393248, 32688385257253280866162737638330823344192] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 206).pointIds 206), (.leaf 5 (Common.fact 207).pointIds 207), B0049]
theorem treeEq0048 : B0048.tree = HexagonCover.NBand.M7700_7900.SplitData.node0048 := by
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
  · exact treeEq0049

def B0047 : Block := .branch 157 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 1742245718635204932932477990050653242753040, 43556142965880123323311949751266331459616, 32688385257253280866162737638330823344192] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0048, (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 0 [] 0)]
theorem treeEq0047 : B0047.tree = HexagonCover.NBand.M7700_7900.SplitData.node0047 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0048
  · rfl
  · rfl

def B0046 : Block := .branch 135 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 1742245718635204932932477990050653242753040, 393248, 32688385257253280866162737638330823344192] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), B0047, (.leaf 6 (Common.fact 196).pointIds 196)]
theorem treeEq0046 : B0046.tree = HexagonCover.NBand.M7700_7900.SplitData.node0046 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0047
  · rfl

def B0045 : Block := .branch 140 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 32688385257253280866162737638330823344192] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0046, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 190).pointIds 190)]
theorem treeEq0045 : B0045.tree = HexagonCover.NBand.M7700_7900.SplitData.node0045 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0046
  · rfl
  · rfl

def B0044 : Block := .branch 113 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 32688374872659563796507480577338164904000] ![(.leaf 0 (Common.fact 222).pointIds 222), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 183).pointIds 183), (.leaf 5 (Common.fact 184).pointIds 184), B0045]
theorem treeEq0044 : B0044.tree = HexagonCover.NBand.M7700_7900.SplitData.node0044 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045

def B0043 : Block := .branch 67 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 32688374872659563796507480577338164904000] ![(.leaf 0 (Common.fact 167).pointIds 167), B0044, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), (.leaf 6 (Common.fact 172).pointIds 172)]
theorem treeEq0043 : B0043.tree = HexagonCover.NBand.M7700_7900.SplitData.node0043 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0044
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0042 : Block := .branch 133 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 165).pointIds 165), (.leaf 5 (Common.fact 166).pointIds 166), B0043]
theorem treeEq0042 : B0042.tree = HexagonCover.NBand.M7700_7900.SplitData.node0042 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0043

def B0041 : Block := .branch 138 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21799339131189532965679493139521582137408] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0042, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 160).pointIds 160)]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M7700_7900.SplitData.node0041 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0042
  · rfl
  · rfl

def B0040 : Block := .branch 124 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 221).pointIds 221), (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), B0041]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M7700_7900.SplitData.node0040 := by
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
  · exact treeEq0041

theorem accepted0040 : B0040.accepted = true := by decide +kernel
theorem checked0040 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0040 (maskNeeds ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0040]
  exact B0040.sound accepted0040
#print axioms checked0040

end HexagonCover.NBand.M7700_7900.SplitTree.Run0004
