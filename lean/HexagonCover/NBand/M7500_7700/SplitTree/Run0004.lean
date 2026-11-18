import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0004
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0396 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0396 : B0396.tree = HexagonCover.NBand.M7500_7700.SplitData.node0396 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0395 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0396]
theorem treeEq0395 : B0395.tree = HexagonCover.NBand.M7500_7700.SplitData.node0395 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0396

def B0394 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0395, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0394 : B0394.tree = HexagonCover.NBand.M7500_7700.SplitData.node0394 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0395
  · rfl
  · rfl

def B0393 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0394]
theorem treeEq0393 : B0393.tree = HexagonCover.NBand.M7500_7700.SplitData.node0393 := by
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
  · exact treeEq0394

def B0392 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0393, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0392 : B0392.tree = HexagonCover.NBand.M7500_7700.SplitData.node0392 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0393
  · rfl
  · rfl

def B0391 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0392, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0391 : B0391.tree = HexagonCover.NBand.M7500_7700.SplitData.node0391 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0392
  · rfl

def B0390 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0391, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0390 : B0390.tree = HexagonCover.NBand.M7500_7700.SplitData.node0390 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0391
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0389 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0390, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0389 : B0389.tree = HexagonCover.NBand.M7500_7700.SplitData.node0389 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0390
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0388 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0389]
theorem treeEq0388 : B0388.tree = HexagonCover.NBand.M7500_7700.SplitData.node0388 := by
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
  · exact treeEq0389

def B0387 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0388]
theorem treeEq0387 : B0387.tree = HexagonCover.NBand.M7500_7700.SplitData.node0387 := by
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
  · exact treeEq0388

def B0386 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0387, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0386 : B0386.tree = HexagonCover.NBand.M7500_7700.SplitData.node0386 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0387
  · rfl
  · rfl

def B0385 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0386, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0385 : B0385.tree = HexagonCover.NBand.M7500_7700.SplitData.node0385 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0386
  · rfl

def B0384 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0385, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0384 : B0384.tree = HexagonCover.NBand.M7500_7700.SplitData.node0384 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0385
  · rfl
  · rfl

def B0383 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0384]
theorem treeEq0383 : B0383.tree = HexagonCover.NBand.M7500_7700.SplitData.node0383 := by
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
  · exact treeEq0384

def B0400 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0400 : B0400.tree = HexagonCover.NBand.M7500_7700.SplitData.node0400 := by
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

def B0399 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0400, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0399 : B0399.tree = HexagonCover.NBand.M7500_7700.SplitData.node0399 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0400
  · rfl
  · rfl

def B0398 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0399, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0398 : B0398.tree = HexagonCover.NBand.M7500_7700.SplitData.node0398 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0399
  · rfl

def B0397 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0398, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0397 : B0397.tree = HexagonCover.NBand.M7500_7700.SplitData.node0397 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0398
  · rfl
  · rfl

def B0382 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0383, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0397]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M7500_7700.SplitData.node0382 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0383
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0397

theorem accepted0382 : B0382.accepted = true := by decide +kernel
theorem checked0382 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0382 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0382]
  exact B0382.sound accepted0382
#print axioms checked0382

def B0435 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M7500_7700.SplitData.node0435 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0434 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0435]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M7500_7700.SplitData.node0434 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0435

def B0433 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0434, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M7500_7700.SplitData.node0433 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0434
  · rfl
  · rfl

def B0432 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0433]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M7500_7700.SplitData.node0432 := by
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
  · exact treeEq0433

def B0431 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0432, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M7500_7700.SplitData.node0431 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0432
  · rfl
  · rfl

def B0430 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0431, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M7500_7700.SplitData.node0430 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0431
  · rfl

def B0429 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0430, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M7500_7700.SplitData.node0429 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0430
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0428 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0429, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M7500_7700.SplitData.node0428 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0429
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0427 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0428]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M7500_7700.SplitData.node0427 := by
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
  · exact treeEq0428

def B0426 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0427]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M7500_7700.SplitData.node0426 := by
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
  · exact treeEq0427

def B0425 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0426, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M7500_7700.SplitData.node0425 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · rfl

def B0424 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0425, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M7500_7700.SplitData.node0424 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0425
  · rfl

def B0423 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0424, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M7500_7700.SplitData.node0423 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0424
  · rfl
  · rfl

def B0422 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0423]
theorem treeEq0422 : B0422.tree = HexagonCover.NBand.M7500_7700.SplitData.node0422 := by
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
  · exact treeEq0423

def B0439 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M7500_7700.SplitData.node0439 := by
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

def B0438 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0439, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M7500_7700.SplitData.node0438 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0439
  · rfl
  · rfl

def B0437 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0438, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M7500_7700.SplitData.node0437 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0438
  · rfl

def B0436 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0437, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M7500_7700.SplitData.node0436 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0437
  · rfl
  · rfl

def B0421 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0422, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0436]
theorem treeEq0421 : B0421.tree = HexagonCover.NBand.M7500_7700.SplitData.node0421 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0422
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0436

theorem accepted0421 : B0421.accepted = true := by decide +kernel
theorem checked0421 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0421 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0421]
  exact B0421.sound accepted0421
#print axioms checked0421

def Tip0381_0382 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0382 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked0382
def B0415 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0415 : B0415.tree = HexagonCover.NBand.M7500_7700.SplitData.node0415 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0414 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0415]
theorem treeEq0414 : B0414.tree = HexagonCover.NBand.M7500_7700.SplitData.node0414 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0415

def B0413 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0414, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0413 : B0413.tree = HexagonCover.NBand.M7500_7700.SplitData.node0413 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0414
  · rfl
  · rfl

def B0412 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0413]
theorem treeEq0412 : B0412.tree = HexagonCover.NBand.M7500_7700.SplitData.node0412 := by
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
  · exact treeEq0413

def B0411 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0412, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0411 : B0411.tree = HexagonCover.NBand.M7500_7700.SplitData.node0411 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0412
  · rfl
  · rfl

def B0410 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0411, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0410 : B0410.tree = HexagonCover.NBand.M7500_7700.SplitData.node0410 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0411
  · rfl

def B0409 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0410, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0409 : B0409.tree = HexagonCover.NBand.M7500_7700.SplitData.node0409 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0410
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0408 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0409, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0408 : B0408.tree = HexagonCover.NBand.M7500_7700.SplitData.node0408 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0409
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0407 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0408]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M7500_7700.SplitData.node0407 := by
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
  · exact treeEq0408

def B0406 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0407]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M7500_7700.SplitData.node0406 := by
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
  · exact treeEq0407

def B0405 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0406, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M7500_7700.SplitData.node0405 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0406
  · rfl
  · rfl

def B0404 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0405, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M7500_7700.SplitData.node0404 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0405
  · rfl

def B0403 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0404, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M7500_7700.SplitData.node0403 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0404
  · rfl
  · rfl

def B0402 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0403]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M7500_7700.SplitData.node0402 := by
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
  · exact treeEq0403

def B0419 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0419 : B0419.tree = HexagonCover.NBand.M7500_7700.SplitData.node0419 := by
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

def B0418 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0419, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0418 : B0418.tree = HexagonCover.NBand.M7500_7700.SplitData.node0418 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0419
  · rfl
  · rfl

def B0417 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0418, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0417 : B0417.tree = HexagonCover.NBand.M7500_7700.SplitData.node0417 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0418
  · rfl

def B0416 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0417, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0416 : B0416.tree = HexagonCover.NBand.M7500_7700.SplitData.node0416 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0417
  · rfl
  · rfl

def B0401 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0402, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0416]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M7500_7700.SplitData.node0401 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0402
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0416

def B0381 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0381_0382, B0401, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M7500_7700.SplitData.node0381 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0401
  · rfl
  · rfl
  · rfl

theorem accepted0381 : B0381.accepted = true := by decide +kernel
theorem checked0381 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0381 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0381]
  exact B0381.sound accepted0381
#print axioms checked0381

def Tip0420_0421 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0421 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked0421
def B0454 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M7500_7700.SplitData.node0454 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0453 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0454]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M7500_7700.SplitData.node0453 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0454

def B0452 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0453, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M7500_7700.SplitData.node0452 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0453
  · rfl
  · rfl

def B0451 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0452]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M7500_7700.SplitData.node0451 := by
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
  · exact treeEq0452

def B0450 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0451, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M7500_7700.SplitData.node0450 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0451
  · rfl
  · rfl

def B0449 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0450, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M7500_7700.SplitData.node0449 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0450
  · rfl

def B0448 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0449, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M7500_7700.SplitData.node0448 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0449
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0447 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0448, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M7500_7700.SplitData.node0447 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0448
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0446 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0447]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M7500_7700.SplitData.node0446 := by
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
  · exact treeEq0447

def B0445 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0446]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M7500_7700.SplitData.node0445 := by
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
  · exact treeEq0446

def B0444 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0445, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M7500_7700.SplitData.node0444 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0445
  · rfl
  · rfl

def B0443 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0444, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M7500_7700.SplitData.node0443 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0444
  · rfl

def B0442 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0443, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M7500_7700.SplitData.node0442 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0443
  · rfl
  · rfl

def B0441 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0442]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M7500_7700.SplitData.node0441 := by
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
  · exact treeEq0442

def B0458 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M7500_7700.SplitData.node0458 := by
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

def B0457 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0458, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M7500_7700.SplitData.node0457 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0458
  · rfl
  · rfl

def B0456 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0457, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M7500_7700.SplitData.node0456 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl

def B0455 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0456, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M7500_7700.SplitData.node0455 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0456
  · rfl
  · rfl

def B0440 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0441, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0455]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M7500_7700.SplitData.node0440 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0441
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0455

def B0420 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0420_0421, B0440, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0420 : B0420.tree = HexagonCover.NBand.M7500_7700.SplitData.node0420 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0440
  · rfl
  · rfl
  · rfl

theorem accepted0420 : B0420.accepted = true := by decide +kernel
theorem checked0420 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0420 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0420]
  exact B0420.sound accepted0420
#print axioms checked0420

end HexagonCover.NBand.M7500_7700.SplitTree.Run0004
