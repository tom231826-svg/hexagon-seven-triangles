import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0003
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0316 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 677).pointIds 677), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0316 : B0316.tree = HexagonCover.NBand.M7500_7700.SplitData.node0316 := by
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

def B0315 : Block := .branch 139 ![385, 1538, 6148, 79266852862858488596779786248, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0316]
theorem treeEq0315 : B0315.tree = HexagonCover.NBand.M7500_7700.SplitData.node0315 := by
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
  · exact treeEq0316

def B0314 : Block := .branch 151 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0315, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0314 : B0314.tree = HexagonCover.NBand.M7500_7700.SplitData.node0314 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0315
  · rfl
  · rfl

def B0313 : Block := .branch 163 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0314]
theorem treeEq0313 : B0313.tree = HexagonCover.NBand.M7500_7700.SplitData.node0313 := by
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
  · exact treeEq0314

def B0312 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 675).pointIds 675), (.leaf 3 (Common.fact 676).pointIds 676), B0313, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0312 : B0312.tree = HexagonCover.NBand.M7500_7700.SplitData.node0312 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0313
  · rfl
  · rfl

def B0311 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 655).pointIds 655), B0312, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0311 : B0311.tree = HexagonCover.NBand.M7500_7700.SplitData.node0311 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0312
  · rfl

def B0310 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0311, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0310 : B0310.tree = HexagonCover.NBand.M7500_7700.SplitData.node0310 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0311
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0309 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0310, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0309 : B0309.tree = HexagonCover.NBand.M7500_7700.SplitData.node0309 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0310
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0308 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0309]
theorem treeEq0308 : B0308.tree = HexagonCover.NBand.M7500_7700.SplitData.node0308 := by
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
  · exact treeEq0309

def B0307 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0308]
theorem treeEq0307 : B0307.tree = HexagonCover.NBand.M7500_7700.SplitData.node0307 := by
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
  · exact treeEq0308

def B0306 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0307, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0306 : B0306.tree = HexagonCover.NBand.M7500_7700.SplitData.node0306 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0307
  · rfl
  · rfl

def B0305 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0306, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0305 : B0305.tree = HexagonCover.NBand.M7500_7700.SplitData.node0305 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0306
  · rfl

def B0304 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0305, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0304 : B0304.tree = HexagonCover.NBand.M7500_7700.SplitData.node0304 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0305
  · rfl
  · rfl

def B0303 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0304]
theorem treeEq0303 : B0303.tree = HexagonCover.NBand.M7500_7700.SplitData.node0303 := by
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
  · exact treeEq0304

def B0320 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0320 : B0320.tree = HexagonCover.NBand.M7500_7700.SplitData.node0320 := by
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

def B0319 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0320, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0319 : B0319.tree = HexagonCover.NBand.M7500_7700.SplitData.node0319 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0320
  · rfl
  · rfl

def B0318 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0319, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0318 : B0318.tree = HexagonCover.NBand.M7500_7700.SplitData.node0318 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0319
  · rfl

def B0317 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0318, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0317 : B0317.tree = HexagonCover.NBand.M7500_7700.SplitData.node0317 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0318
  · rfl
  · rfl

def B0302 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0303, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0317]
theorem treeEq0302 : B0302.tree = HexagonCover.NBand.M7500_7700.SplitData.node0302 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0303
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0317

theorem accepted0302 : B0302.accepted = true := by decide +kernel
theorem checked0302 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0302 (maskNeeds ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0302]
  exact B0302.sound accepted0302
#print axioms checked0302

def B0355 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 677).pointIds 677), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0355 : B0355.tree = HexagonCover.NBand.M7500_7700.SplitData.node0355 := by
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

def B0354 : Block := .branch 139 ![385, 1538, 6148, 79266852862858488596779786248, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0355]
theorem treeEq0354 : B0354.tree = HexagonCover.NBand.M7500_7700.SplitData.node0354 := by
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
  · exact treeEq0355

def B0353 : Block := .branch 151 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0354, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0353 : B0353.tree = HexagonCover.NBand.M7500_7700.SplitData.node0353 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0354
  · rfl
  · rfl

def B0352 : Block := .branch 163 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0353]
theorem treeEq0352 : B0352.tree = HexagonCover.NBand.M7500_7700.SplitData.node0352 := by
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
  · exact treeEq0353

def B0351 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 675).pointIds 675), (.leaf 3 (Common.fact 676).pointIds 676), B0352, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0351 : B0351.tree = HexagonCover.NBand.M7500_7700.SplitData.node0351 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0352
  · rfl
  · rfl

def B0350 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 655).pointIds 655), B0351, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0350 : B0350.tree = HexagonCover.NBand.M7500_7700.SplitData.node0350 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0351
  · rfl

def B0349 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0350, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0349 : B0349.tree = HexagonCover.NBand.M7500_7700.SplitData.node0349 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0350
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0348 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0349, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0348 : B0348.tree = HexagonCover.NBand.M7500_7700.SplitData.node0348 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0349
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0347 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0348]
theorem treeEq0347 : B0347.tree = HexagonCover.NBand.M7500_7700.SplitData.node0347 := by
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
  · exact treeEq0348

def B0346 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0347]
theorem treeEq0346 : B0346.tree = HexagonCover.NBand.M7500_7700.SplitData.node0346 := by
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
  · exact treeEq0347

def B0345 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0346, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0345 : B0345.tree = HexagonCover.NBand.M7500_7700.SplitData.node0345 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0346
  · rfl
  · rfl

def B0344 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0345, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0344 : B0344.tree = HexagonCover.NBand.M7500_7700.SplitData.node0344 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0345
  · rfl

def B0343 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0344, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0343 : B0343.tree = HexagonCover.NBand.M7500_7700.SplitData.node0343 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0344
  · rfl
  · rfl

def B0342 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0343]
theorem treeEq0342 : B0342.tree = HexagonCover.NBand.M7500_7700.SplitData.node0342 := by
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
  · exact treeEq0343

def B0359 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0359 : B0359.tree = HexagonCover.NBand.M7500_7700.SplitData.node0359 := by
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

def B0358 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0359, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0358 : B0358.tree = HexagonCover.NBand.M7500_7700.SplitData.node0358 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0359
  · rfl
  · rfl

def B0357 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0358, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0357 : B0357.tree = HexagonCover.NBand.M7500_7700.SplitData.node0357 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0358
  · rfl

def B0356 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0357, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0356 : B0356.tree = HexagonCover.NBand.M7500_7700.SplitData.node0356 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0357
  · rfl
  · rfl

def B0341 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0342, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0356]
theorem treeEq0341 : B0341.tree = HexagonCover.NBand.M7500_7700.SplitData.node0341 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0342
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0356

theorem accepted0341 : B0341.accepted = true := by decide +kernel
theorem checked0341 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0341 (maskNeeds ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0341]
  exact B0341.sound accepted0341
#print axioms checked0341

def Tip0301_0302 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0302 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] checked0302
def B0335 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 677).pointIds 677), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0335 : B0335.tree = HexagonCover.NBand.M7500_7700.SplitData.node0335 := by
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

def B0334 : Block := .branch 139 ![385, 1538, 6148, 79266852862858488596779786248, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0335]
theorem treeEq0334 : B0334.tree = HexagonCover.NBand.M7500_7700.SplitData.node0334 := by
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
  · exact treeEq0335

def B0333 : Block := .branch 151 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0334, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0333 : B0333.tree = HexagonCover.NBand.M7500_7700.SplitData.node0333 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0334
  · rfl
  · rfl

def B0332 : Block := .branch 163 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0333]
theorem treeEq0332 : B0332.tree = HexagonCover.NBand.M7500_7700.SplitData.node0332 := by
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
  · exact treeEq0333

def B0331 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 675).pointIds 675), (.leaf 3 (Common.fact 676).pointIds 676), B0332, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0331 : B0331.tree = HexagonCover.NBand.M7500_7700.SplitData.node0331 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0332
  · rfl
  · rfl

def B0330 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 655).pointIds 655), B0331, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0330 : B0330.tree = HexagonCover.NBand.M7500_7700.SplitData.node0330 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0331
  · rfl

def B0329 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0330, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0329 : B0329.tree = HexagonCover.NBand.M7500_7700.SplitData.node0329 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0330
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0328 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0329, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0328 : B0328.tree = HexagonCover.NBand.M7500_7700.SplitData.node0328 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0329
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0327 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0328]
theorem treeEq0327 : B0327.tree = HexagonCover.NBand.M7500_7700.SplitData.node0327 := by
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
  · exact treeEq0328

def B0326 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0327]
theorem treeEq0326 : B0326.tree = HexagonCover.NBand.M7500_7700.SplitData.node0326 := by
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
  · exact treeEq0327

def B0325 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0326, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0325 : B0325.tree = HexagonCover.NBand.M7500_7700.SplitData.node0325 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0326
  · rfl
  · rfl

def B0324 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0325, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0324 : B0324.tree = HexagonCover.NBand.M7500_7700.SplitData.node0324 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0325
  · rfl

def B0323 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0324, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0323 : B0323.tree = HexagonCover.NBand.M7500_7700.SplitData.node0323 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0324
  · rfl
  · rfl

def B0322 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0323]
theorem treeEq0322 : B0322.tree = HexagonCover.NBand.M7500_7700.SplitData.node0322 := by
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
  · exact treeEq0323

def B0339 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0339 : B0339.tree = HexagonCover.NBand.M7500_7700.SplitData.node0339 := by
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

def B0338 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0339, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0338 : B0338.tree = HexagonCover.NBand.M7500_7700.SplitData.node0338 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0339
  · rfl
  · rfl

def B0337 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0338, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0337 : B0337.tree = HexagonCover.NBand.M7500_7700.SplitData.node0337 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0338
  · rfl

def B0336 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0337, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0336 : B0336.tree = HexagonCover.NBand.M7500_7700.SplitData.node0336 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0337
  · rfl
  · rfl

def B0321 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0322, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0336]
theorem treeEq0321 : B0321.tree = HexagonCover.NBand.M7500_7700.SplitData.node0321 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0322
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0336

def B0301 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0301_0302, B0321, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0301 : B0301.tree = HexagonCover.NBand.M7500_7700.SplitData.node0301 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0321
  · rfl
  · rfl
  · rfl

theorem accepted0301 : B0301.accepted = true := by decide +kernel
theorem checked0301 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0301 (maskNeeds ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0301]
  exact B0301.sound accepted0301
#print axioms checked0301

def Tip0340_0341 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0341 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] checked0341
def B0374 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 2993338754582201892325862527150021884380375031054352, 393248, 718676358937339411712218960264421480857664] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 677).pointIds 677), (.leaf 4 (Common.fact 666).pointIds 666), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M7500_7700.SplitData.node0374 := by
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

def B0373 : Block := .branch 139 ![385, 1538, 6148, 79266852862858488596779786248, 2993341609077587304245624643721960783370647796547600, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 94).pointIds 94), (.leaf 1 (Common.fact 95).pointIds 95), (.leaf 2 (Common.fact 96).pointIds 96), (.leaf 3 (Common.fact 97).pointIds 97), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 98).pointIds 98), B0374]
theorem treeEq0373 : B0373.tree = HexagonCover.NBand.M7500_7700.SplitData.node0373 := by
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
  · exact treeEq0374

def B0372 : Block := .branch 151 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 11692013125869812699621932616372022120315935522880] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), B0373, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0372 : B0372.tree = HexagonCover.NBand.M7500_7700.SplitData.node0372 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0373
  · rfl
  · rfl

def B0371 : Block := .branch 163 ![385, 1538, 6148, 79266852862858488596779786248, 2993338754582201892325862527150021884380375031054352, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 284).pointIds 284), B0372]
theorem treeEq0371 : B0371.tree = HexagonCover.NBand.M7500_7700.SplitData.node0371 := by
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
  · exact treeEq0372

def B0370 : Block := .branch 171 ![590295810358705652097, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 1496577676626887123536438386009406733953603895427104, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 657).pointIds 657), (.leaf 1 (Common.fact 658).pointIds 658), (.leaf 2 (Common.fact 675).pointIds 675), (.leaf 3 (Common.fact 676).pointIds 676), B0371, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0370 : B0370.tree = HexagonCover.NBand.M7500_7700.SplitData.node0370 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0371
  · rfl
  · rfl

def B0369 : Block := .branch 170 ![748288838313422294120286634955790111681510755008897, 148222470936017765890, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 600).pointIds 600), (.leaf 1 (Common.fact 652).pointIds 652), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 655).pointIds 655), B0370, (.leaf 6 (Common.fact 656).pointIds 656)]
theorem treeEq0369 : B0369.tree = HexagonCover.NBand.M7500_7700.SplitData.node0369 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0370
  · rfl

def B0368 : Block := .branch 79 ![748288838313422294120286634351327201874196167655809, 148366586124093621762, 2398076729582241716228, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0369, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 464).pointIds 464)]
theorem treeEq0368 : B0368.tree = HexagonCover.NBand.M7500_7700.SplitData.node0368 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0369
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0367 : Block := .branch 169 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 27222589353992453954641757963068475179072] ![B0368, (.leaf 1 (Common.fact 458).pointIds 458), (.leaf 2 (Common.fact 459).pointIds 459), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 462).pointIds 462), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0367 : B0367.tree = HexagonCover.NBand.M7500_7700.SplitData.node0367 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0368
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0366 : Block := .branch 132 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 219).pointIds 219), B0367]
theorem treeEq0366 : B0366.tree = HexagonCover.NBand.M7500_7700.SplitData.node0366 := by
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
  · exact treeEq0367

def B0365 : Block := .branch 133 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 183401328512715844715989747074260125025183039504, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 456).pointIds 456), (.leaf 5 (Common.fact 198).pointIds 198), B0366]
theorem treeEq0365 : B0365.tree = HexagonCover.NBand.M7500_7700.SplitData.node0365 := by
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
  · exact treeEq0366

def B0364 : Block := .branch 157 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0365, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0364 : B0364.tree = HexagonCover.NBand.M7500_7700.SplitData.node0364 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0365
  · rfl
  · rfl

def B0363 : Block := .branch 125 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0364, (.leaf 6 (Common.fact 455).pointIds 455)]
theorem treeEq0363 : B0363.tree = HexagonCover.NBand.M7500_7700.SplitData.node0363 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0364
  · rfl

def B0362 : Block := .branch 149 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0363, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 453).pointIds 453)]
theorem treeEq0362 : B0362.tree = HexagonCover.NBand.M7500_7700.SplitData.node0362 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0363
  · rfl
  · rfl

def B0361 : Block := .branch 88 ![590295810358705652097, 302380109720157539010050, 2416559502452970231812, 79266852862858488596779786248, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0362]
theorem treeEq0361 : B0361.tree = HexagonCover.NBand.M7500_7700.SplitData.node0361 := by
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
  · exact treeEq0362

def B0378 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M7500_7700.SplitData.node0378 := by
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

def B0377 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0378, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M7500_7700.SplitData.node0377 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0378
  · rfl
  · rfl

def B0376 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0377, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M7500_7700.SplitData.node0376 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0377
  · rfl

def B0375 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0376, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M7500_7700.SplitData.node0375 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0376
  · rfl
  · rfl

def B0360 : Block := .branch 78 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), B0361, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0375]
theorem treeEq0360 : B0360.tree = HexagonCover.NBand.M7500_7700.SplitData.node0360 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0361
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0375

def B0340 : Block := .branch 74 ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0340_0341, B0360, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0340 : B0340.tree = HexagonCover.NBand.M7500_7700.SplitData.node0340 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0360
  · rfl
  · rfl
  · rfl

theorem accepted0340 : B0340.accepted = true := by decide +kernel
theorem checked0340 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0340 (maskNeeds ![590295810358705652097, 148654816500245333506, 2416559502452970231812, 79286195675972322663575085064, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0340]
  exact B0340.sound accepted0340
#print axioms checked0340

end HexagonCover.NBand.M7500_7700.SplitTree.Run0003
