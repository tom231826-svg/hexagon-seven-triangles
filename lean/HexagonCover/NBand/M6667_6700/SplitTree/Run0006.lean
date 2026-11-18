import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0486 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0486 : B0486.tree = HexagonCover.NBand.M6667_6700.SplitData.node0486 := by
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

def B0485 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0486]
theorem treeEq0485 : B0485.tree = HexagonCover.NBand.M6667_6700.SplitData.node0485 := by
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
  · exact treeEq0486

def B0488 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq0488 : B0488.tree = HexagonCover.NBand.M6667_6700.SplitData.node0488 := by
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
  · rfl

def B0487 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0488, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0487 : B0487.tree = HexagonCover.NBand.M6667_6700.SplitData.node0487 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0488
  · rfl
  · rfl

def B0484 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0485, (.leaf 5 (Common.fact 439).pointIds 439), B0487]
theorem treeEq0484 : B0484.tree = HexagonCover.NBand.M6667_6700.SplitData.node0484 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0485
  · rfl
  · exact treeEq0487

def B0490 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M6667_6700.SplitData.node0490 := by
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

def B0489 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0490]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M6667_6700.SplitData.node0489 := by
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
  · exact treeEq0490

def B0483 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0484, B0489, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0483 : B0483.tree = HexagonCover.NBand.M6667_6700.SplitData.node0483 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0484
  · exact treeEq0489
  · rfl
  · rfl

def B0493 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M6667_6700.SplitData.node0493 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0492 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0493]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M6667_6700.SplitData.node0492 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0493

def B0491 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0492, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M6667_6700.SplitData.node0491 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0492
  · rfl
  · rfl

def B0482 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0483, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0491, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M6667_6700.SplitData.node0482 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0483
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0491
  · rfl

def B0496 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M6667_6700.SplitData.node0496 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0495 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0496]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M6667_6700.SplitData.node0495 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0496

def B0494 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0495, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M6667_6700.SplitData.node0494 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0495
  · rfl
  · rfl

def B0481 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0482, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0494]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M6667_6700.SplitData.node0481 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0482
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0494

theorem accepted0481 : B0481.accepted = true := by decide +kernel
theorem checked0481 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0481 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq0481]
  exact B0481.sound accepted0481
#print axioms checked0481

def B0519 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0519 : B0519.tree = HexagonCover.NBand.M6667_6700.SplitData.node0519 := by
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

def B0518 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0519]
theorem treeEq0518 : B0518.tree = HexagonCover.NBand.M6667_6700.SplitData.node0518 := by
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
  · exact treeEq0519

def B0521 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M6667_6700.SplitData.node0521 := by
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
  · rfl

def B0520 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0521, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M6667_6700.SplitData.node0520 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0521
  · rfl
  · rfl

def B0517 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0518, (.leaf 5 (Common.fact 439).pointIds 439), B0520]
theorem treeEq0517 : B0517.tree = HexagonCover.NBand.M6667_6700.SplitData.node0517 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0518
  · rfl
  · exact treeEq0520

def B0523 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M6667_6700.SplitData.node0523 := by
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

def B0522 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0523]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M6667_6700.SplitData.node0522 := by
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
  · exact treeEq0523

def B0516 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0517, B0522, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0516 : B0516.tree = HexagonCover.NBand.M6667_6700.SplitData.node0516 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0517
  · exact treeEq0522
  · rfl
  · rfl

def B0526 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M6667_6700.SplitData.node0526 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0525 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0526]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M6667_6700.SplitData.node0525 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0526

def B0524 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0525, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M6667_6700.SplitData.node0524 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0525
  · rfl
  · rfl

def B0515 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0516, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0524, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M6667_6700.SplitData.node0515 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0516
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0524
  · rfl

def B0529 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M6667_6700.SplitData.node0529 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0528 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0529]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M6667_6700.SplitData.node0528 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0529

def B0527 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0528, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M6667_6700.SplitData.node0527 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl
  · rfl

def B0514 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0515, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0527]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M6667_6700.SplitData.node0514 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0515
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0527

theorem accepted0514 : B0514.accepted = true := by decide +kernel
theorem checked0514 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0514 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq0514]
  exact B0514.sound accepted0514
#print axioms checked0514

def Tip0480_0481 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0481 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] checked0481
def B0502 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M6667_6700.SplitData.node0502 := by
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

def B0501 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0502]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M6667_6700.SplitData.node0501 := by
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
  · exact treeEq0502

def B0504 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M6667_6700.SplitData.node0504 := by
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
  · rfl

def B0503 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0504, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M6667_6700.SplitData.node0503 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0504
  · rfl
  · rfl

def B0500 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0501, (.leaf 5 (Common.fact 439).pointIds 439), B0503]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M6667_6700.SplitData.node0500 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl
  · exact treeEq0503

def B0506 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M6667_6700.SplitData.node0506 := by
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

def B0505 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0506]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M6667_6700.SplitData.node0505 := by
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
  · exact treeEq0506

def B0499 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0500, B0505, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M6667_6700.SplitData.node0499 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0500
  · exact treeEq0505
  · rfl
  · rfl

def B0509 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M6667_6700.SplitData.node0509 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0508 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0509]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M6667_6700.SplitData.node0508 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0509

def B0507 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0508, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M6667_6700.SplitData.node0507 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0508
  · rfl
  · rfl

def B0498 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0499, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0507, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M6667_6700.SplitData.node0498 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0499
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0507
  · rfl

def B0512 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M6667_6700.SplitData.node0512 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0511 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0512]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M6667_6700.SplitData.node0511 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0512

def B0510 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0511, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M6667_6700.SplitData.node0510 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0511
  · rfl
  · rfl

def B0497 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0498, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0510]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M6667_6700.SplitData.node0497 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0510

def B0480 : Block := .branch 74 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), Tip0480_0481, B0497, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 925).pointIds 925)]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M6667_6700.SplitData.node0480 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0497
  · rfl
  · rfl
  · rfl

theorem accepted0480 : B0480.accepted = true := by decide +kernel
theorem checked0480 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0480 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762740047737080285592112168127727276654656]) := by
  rw [← treeEq0480]
  exact B0480.sound accepted0480
#print axioms checked0480

def B0553 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M6667_6700.SplitData.node0553 := by
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

def B0552 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0553]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M6667_6700.SplitData.node0552 := by
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
  · exact treeEq0553

def B0555 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 930).pointIds 930)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M6667_6700.SplitData.node0555 := by
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
  · rfl

def B0554 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634482129318734510085898304] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), B0555, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M6667_6700.SplitData.node0554 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0555
  · rfl
  · rfl

def B0551 : Block := .branch 128 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), B0552, (.leaf 5 (Common.fact 439).pointIds 439), B0554]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M6667_6700.SplitData.node0551 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0552
  · rfl
  · exact treeEq0554

def B0557 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222827339302094445919862848] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 928).pointIds 928)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M6667_6700.SplitData.node0557 := by
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

def B0556 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 9671406556917033397673992, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588476602396030608457859136] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0557]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M6667_6700.SplitData.node0556 := by
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
  · exact treeEq0557

def B0550 : Block := .branch 127 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715760366360513606715965504] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0551, B0556, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 927).pointIds 927)]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M6667_6700.SplitData.node0550 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0551
  · exact treeEq0556
  · rfl
  · rfl

def B0560 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233421613568382428165701696] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq0560 : B0560.tree = HexagonCover.NBand.M6667_6700.SplitData.node0560 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0559 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699696018665944127078317686848] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0560]
theorem treeEq0559 : B0559.tree = HexagonCover.NBand.M6667_6700.SplitData.node0559 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0560

def B0558 : Block := .branch 167 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724667090823302429908610076575793216] ![(.leaf 0 (Common.fact 839).pointIds 839), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 931).pointIds 931), (.leaf 3 (Common.fact 932).pointIds 932), B0559, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 933).pointIds 933)]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M6667_6700.SplitData.node0558 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0559
  · rfl
  · rfl

def B0549 : Block := .branch 125 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0550, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0558, (.leaf 6 (Common.fact 926).pointIds 926)]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M6667_6700.SplitData.node0549 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0550
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0558
  · rfl

def B0563 : Block := .branch 128 ![385, 1538, 6148, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq0563 : B0563.tree = HexagonCover.NBand.M6667_6700.SplitData.node0563 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0562 : Block := .branch 171 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 19342813113834066795323400, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 864).pointIds 864), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 908).pointIds 908), (.leaf 3 (Common.fact 763).pointIds 763), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0563]
theorem treeEq0562 : B0562.tree = HexagonCover.NBand.M6667_6700.SplitData.node0562 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0563

def B0561 : Block := .branch 169 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 867).pointIds 867), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 900).pointIds 900), B0562, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq0561 : B0561.tree = HexagonCover.NBand.M6667_6700.SplitData.node0561 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0562
  · rfl
  · rfl

def B0548 : Block := .branch 123 ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504] ![B0549, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0561]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M6667_6700.SplitData.node0548 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0549
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0561

theorem accepted0548 : B0548.accepted = true := by decide +kernel
theorem checked0548 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0548 (maskNeeds ![4951760158294442604203344257, 147573953689188042242, 2398076729582241716228, 29014219670751100192972808, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389281088715760366360513606715965504]) := by
  rw [← treeEq0548]
  exact B0548.sound accepted0548
#print axioms checked0548

end HexagonCover.NBand.M6667_6700.SplitTree.Run0006
