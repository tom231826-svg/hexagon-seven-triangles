import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0475 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M7500_7700.SplitData.node0475 := by
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

def B0474 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0475]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M7500_7700.SplitData.node0474 := by
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
  · exact treeEq0475

def B0473 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0474, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M7500_7700.SplitData.node0473 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0474
  · rfl
  · rfl

def B0472 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0473]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M7500_7700.SplitData.node0472 := by
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
  · exact treeEq0473

def B0471 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0472, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M7500_7700.SplitData.node0471 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0472
  · rfl
  · rfl

def B0470 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0471, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M7500_7700.SplitData.node0470 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0471
  · rfl

def B0469 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0470, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M7500_7700.SplitData.node0469 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0470
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0468 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0469, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M7500_7700.SplitData.node0468 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0469
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0467 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0468]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M7500_7700.SplitData.node0467 := by
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
  · exact treeEq0468

def B0466 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0467]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M7500_7700.SplitData.node0466 := by
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
  · exact treeEq0467

def B0465 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0466, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M7500_7700.SplitData.node0465 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0466
  · rfl
  · rfl

def B0464 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0465, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M7500_7700.SplitData.node0464 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0465
  · rfl

def B0463 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0464, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M7500_7700.SplitData.node0463 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0464
  · rfl
  · rfl

def B0462 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0463]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M7500_7700.SplitData.node0462 := by
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
  · exact treeEq0463

def B0479 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0479 : B0479.tree = HexagonCover.NBand.M7500_7700.SplitData.node0479 := by
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

def B0478 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0479, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M7500_7700.SplitData.node0478 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0479
  · rfl
  · rfl

def B0477 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0478, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M7500_7700.SplitData.node0477 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0478
  · rfl

def B0476 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0477, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M7500_7700.SplitData.node0476 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0477
  · rfl
  · rfl

def B0461 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0462, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0476]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M7500_7700.SplitData.node0461 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0462
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0476

theorem accepted0461 : B0461.accepted = true := by decide +kernel
theorem checked0461 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0461 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0461]
  exact B0461.sound accepted0461
#print axioms checked0461

def B0514 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M7500_7700.SplitData.node0514 := by
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

def B0513 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0514]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M7500_7700.SplitData.node0513 := by
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
  · exact treeEq0514

def B0512 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0513, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M7500_7700.SplitData.node0512 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0513
  · rfl
  · rfl

def B0511 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0512]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M7500_7700.SplitData.node0511 := by
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
  · exact treeEq0512

def B0510 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0511, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M7500_7700.SplitData.node0510 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0511
  · rfl
  · rfl

def B0509 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0510, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M7500_7700.SplitData.node0509 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0510
  · rfl

def B0508 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0509, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M7500_7700.SplitData.node0508 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0507 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0508, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M7500_7700.SplitData.node0507 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0508
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0506 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0507]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M7500_7700.SplitData.node0506 := by
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
  · exact treeEq0507

def B0505 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0506]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M7500_7700.SplitData.node0505 := by
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
  · exact treeEq0506

def B0504 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0505, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M7500_7700.SplitData.node0504 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0505
  · rfl
  · rfl

def B0503 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0504, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M7500_7700.SplitData.node0503 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0504
  · rfl

def B0502 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0503, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M7500_7700.SplitData.node0502 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0503
  · rfl
  · rfl

def B0501 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0502]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M7500_7700.SplitData.node0501 := by
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
  · exact treeEq0502

def B0518 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0518 : B0518.tree = HexagonCover.NBand.M7500_7700.SplitData.node0518 := by
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

def B0517 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0518, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0517 : B0517.tree = HexagonCover.NBand.M7500_7700.SplitData.node0517 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0518
  · rfl
  · rfl

def B0516 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0517, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0516 : B0516.tree = HexagonCover.NBand.M7500_7700.SplitData.node0516 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0517
  · rfl

def B0515 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0516, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M7500_7700.SplitData.node0515 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0516
  · rfl
  · rfl

def B0500 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0501, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0515]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M7500_7700.SplitData.node0500 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0501
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0515

theorem accepted0500 : B0500.accepted = true := by decide +kernel
theorem checked0500 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0500 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0500]
  exact B0500.sound accepted0500
#print axioms checked0500

def Tip0460_0461 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0461 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked0461
def B0494 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M7500_7700.SplitData.node0494 := by
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

def B0493 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0494]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M7500_7700.SplitData.node0493 := by
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
  · exact treeEq0494

def B0492 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0493, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M7500_7700.SplitData.node0492 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0493
  · rfl
  · rfl

def B0491 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0492]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M7500_7700.SplitData.node0491 := by
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
  · exact treeEq0492

def B0490 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0491, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M7500_7700.SplitData.node0490 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0491
  · rfl
  · rfl

def B0489 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0490, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M7500_7700.SplitData.node0489 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0490
  · rfl

def B0488 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0489, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0488 : B0488.tree = HexagonCover.NBand.M7500_7700.SplitData.node0488 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0489
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0487 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0488, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0487 : B0487.tree = HexagonCover.NBand.M7500_7700.SplitData.node0487 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0488
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0486 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0487]
theorem treeEq0486 : B0486.tree = HexagonCover.NBand.M7500_7700.SplitData.node0486 := by
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
  · exact treeEq0487

def B0485 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0486]
theorem treeEq0485 : B0485.tree = HexagonCover.NBand.M7500_7700.SplitData.node0485 := by
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
  · exact treeEq0486

def B0484 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0485, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0484 : B0484.tree = HexagonCover.NBand.M7500_7700.SplitData.node0484 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0485
  · rfl
  · rfl

def B0483 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0484, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0483 : B0483.tree = HexagonCover.NBand.M7500_7700.SplitData.node0483 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0484
  · rfl

def B0482 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0483, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M7500_7700.SplitData.node0482 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0483
  · rfl
  · rfl

def B0481 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0482]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M7500_7700.SplitData.node0481 := by
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
  · exact treeEq0482

def B0498 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M7500_7700.SplitData.node0498 := by
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

def B0497 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0498, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M7500_7700.SplitData.node0497 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0498
  · rfl
  · rfl

def B0496 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0497, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M7500_7700.SplitData.node0496 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0497
  · rfl

def B0495 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0496, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M7500_7700.SplitData.node0495 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0496
  · rfl
  · rfl

def B0480 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0481, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0495]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M7500_7700.SplitData.node0480 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0481
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0495

def B0460 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0460_0461, B0480, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M7500_7700.SplitData.node0460 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0480
  · rfl
  · rfl
  · rfl

theorem accepted0460 : B0460.accepted = true := by decide +kernel
theorem checked0460 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0460 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0460]
  exact B0460.sound accepted0460
#print axioms checked0460

def Tip0499_0500 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0500 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] checked0500
def B0533 : Block := .branch 162 ![385, 1538, 6148, 38687987410909568413229064, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0533 : B0533.tree = HexagonCover.NBand.M7500_7700.SplitData.node0533 := by
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

def B0532 : Block := .branch 139 ![385, 1538, 6148, 79266850501675247161957179400, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0533]
theorem treeEq0532 : B0532.tree = HexagonCover.NBand.M7500_7700.SplitData.node0532 := by
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
  · exact treeEq0533

def B0531 : Block := .branch 151 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0532, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0531 : B0531.tree = HexagonCover.NBand.M7500_7700.SplitData.node0531 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0532
  · rfl
  · rfl

def B0530 : Block := .branch 163 ![385, 1538, 6148, 79266850501675247161957179400, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0531]
theorem treeEq0530 : B0530.tree = HexagonCover.NBand.M7500_7700.SplitData.node0530 := by
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
  · exact treeEq0531

def B0529 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 680).pointIds 680), (.leaf 3 (Common.fact 681).pointIds 681), B0530, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M7500_7700.SplitData.node0529 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530
  · rfl
  · rfl

def B0528 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 678).pointIds 678), (.leaf 3 (Common.fact 679).pointIds 679), (.leaf 4 (Common.fact 655).pointIds 655), B0529, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M7500_7700.SplitData.node0528 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0529
  · rfl

def B0527 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 36893488147419109380, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0528, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M7500_7700.SplitData.node0527 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0526 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0527, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M7500_7700.SplitData.node0526 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0527
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0525 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0526]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M7500_7700.SplitData.node0525 := by
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
  · exact treeEq0526

def B0524 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0525]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M7500_7700.SplitData.node0524 := by
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
  · exact treeEq0525

def B0523 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0524, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M7500_7700.SplitData.node0523 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0524
  · rfl
  · rfl

def B0522 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0523, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M7500_7700.SplitData.node0522 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0523
  · rfl

def B0521 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0522, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M7500_7700.SplitData.node0521 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0522
  · rfl
  · rfl

def B0520 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 55376261018147624964, 79266850501675247161957179400, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0521]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M7500_7700.SplitData.node0520 := by
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
  · exact treeEq0521

def B0537 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0537 : B0537.tree = HexagonCover.NBand.M7500_7700.SplitData.node0537 := by
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

def B0536 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0537, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0536 : B0536.tree = HexagonCover.NBand.M7500_7700.SplitData.node0536 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0537
  · rfl
  · rfl

def B0535 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0536, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0535 : B0535.tree = HexagonCover.NBand.M7500_7700.SplitData.node0535 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0536
  · rfl

def B0534 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0535, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0534 : B0534.tree = HexagonCover.NBand.M7500_7700.SplitData.node0534 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0535
  · rfl
  · rfl

def B0519 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0520, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0534]
theorem treeEq0519 : B0519.tree = HexagonCover.NBand.M7500_7700.SplitData.node0519 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0520
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0534

def B0499 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0499_0500, B0519, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M7500_7700.SplitData.node0499 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0519
  · rfl
  · rfl
  · rfl

theorem accepted0499 : B0499.accepted = true := by decide +kernel
theorem checked0499 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0499 (maskNeeds ![590295810358705652097, 148654816500245333506, 55376261018147624964, 79286193314789081228752478216, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0499]
  exact B0499.sound accepted0499
#print axioms checked0499

end HexagonCover.NBand.M7500_7700.SplitTree.Run0005
