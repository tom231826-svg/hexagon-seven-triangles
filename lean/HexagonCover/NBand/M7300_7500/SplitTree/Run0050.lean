import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0049
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0050
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2915_2920 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2920 ![385, 147790266109278553602, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] HexagonCover.NBand.M7300_7500.SplitTree.Run0049.checked2920
def B2917 : Block := .branch 102 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 936).pointIds 936), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), (.leaf 3 (Common.fact 313).pointIds 313), (.leaf 4 (Common.fact 314).pointIds 314), (.leaf 5 (Common.fact 315).pointIds 315), (.leaf 6 (Common.fact 935).pointIds 935)]
theorem treeEq2917 : B2917.tree = HexagonCover.NBand.M7300_7500.SplitData.node2917 := by
  change Tree.branch (102 : Fin 172) _ = Tree.branch (102 : Fin 172) _
  apply congrArg (Tree.branch (102 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2916 : Block := .branch 168 ![576460752303423873, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 369).pointIds 369), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B2917]
theorem treeEq2916 : B2916.tree = HexagonCover.NBand.M7300_7500.SplitData.node2916 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2917

def B3551 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq3551 : B3551.tree = HexagonCover.NBand.M7300_7500.SplitData.node3551 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3550 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B3551, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 981).pointIds 981)]
theorem treeEq3550 : B3550.tree = HexagonCover.NBand.M7300_7500.SplitData.node3550 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3551
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3549 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 753).pointIds 753), B3550, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq3549 : B3549.tree = HexagonCover.NBand.M7300_7500.SplitData.node3549 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3550
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3548 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3549]
theorem treeEq3548 : B3548.tree = HexagonCover.NBand.M7300_7500.SplitData.node3548 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3549

def B3547 : Block := .branch 169 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257129054365516851681135427648] ![B3548, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 980).pointIds 980)]
theorem treeEq3547 : B3547.tree = HexagonCover.NBand.M7300_7500.SplitData.node3547 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3548
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3546 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3547, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3546 : B3546.tree = HexagonCover.NBand.M7300_7500.SplitData.node3546 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3547
  · rfl

def B3545 : Block := .branch 171 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354479631552429487030336] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3546, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq3545 : B3545.tree = HexagonCover.NBand.M7300_7500.SplitData.node3545 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3546
  · rfl
  · rfl

def B2919 : Block := .branch 67 ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 198).pointIds 198), Tip2915_2920, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B3545]
theorem treeEq2919 : B2919.tree = HexagonCover.NBand.M7300_7500.SplitData.node2919 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3545

def B3557 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141509827966273026, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 983).pointIds 983), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq3557 : B3557.tree = HexagonCover.NBand.M7300_7500.SplitData.node3557 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3556 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B3557, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq3556 : B3556.tree = HexagonCover.NBand.M7300_7500.SplitData.node3556 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3557
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3555 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3556]
theorem treeEq3555 : B3555.tree = HexagonCover.NBand.M7300_7500.SplitData.node3555 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3556

def B3554 : Block := .branch 169 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974311749925714704515727424] ![B3555, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 982).pointIds 982)]
theorem treeEq3554 : B3554.tree = HexagonCover.NBand.M7300_7500.SplitData.node3554 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3555
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3553 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3554, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3553 : B3553.tree = HexagonCover.NBand.M7300_7500.SplitData.node3553 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3554
  · rfl

def B3552 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354368951087987229720640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3553, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq3552 : B3552.tree = HexagonCover.NBand.M7300_7500.SplitData.node3552 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3553
  · rfl
  · rfl

def B2918 : Block := .branch 65 ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B2919, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B3552]
theorem treeEq2918 : B2918.tree = HexagonCover.NBand.M7300_7500.SplitData.node2918 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2919
  · rfl
  · rfl
  · rfl
  · exact treeEq3552

def B2915 : Block := .branch 59 ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![B2916, B2918, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq2915 : B2915.tree = HexagonCover.NBand.M7300_7500.SplitData.node2915 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2916
  · exact treeEq2918
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2915 : B2915.accepted = true := by decide +kernel
theorem checked2915 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2915 (maskNeeds ![385, 216313519602140674, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq2915]
  exact B2915.sound accepted2915
#print axioms checked2915

def B3601 : Block := .branch 121 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 739).pointIds 739), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq3601 : B3601.tree = HexagonCover.NBand.M7300_7500.SplitData.node3601 := by
  change Tree.branch (121 : Fin 172) _ = Tree.branch (121 : Fin 172) _
  apply congrArg (Tree.branch (121 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3600 : Block := .branch 168 ![748288838313464829418687052859126286692759839441281, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 734).pointIds 734), (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3601]
theorem treeEq3600 : B3600.tree = HexagonCover.NBand.M7300_7500.SplitData.node3600 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3601

def B3599 : Block := .branch 125 ![748288838313422294122821935551193364866830868414849, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B3600, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3599 : B3599.tree = HexagonCover.NBand.M7300_7500.SplitData.node3599 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3600
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3598 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3599]
theorem treeEq3598 : B3598.tree = HexagonCover.NBand.M7300_7500.SplitData.node3598 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3599

def B3597 : Block := .branch 169 ![2535301200456458802993406411137, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B3598, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq3597 : B3597.tree = HexagonCover.NBand.M7300_7500.SplitData.node3597 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3598
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3596 : Block := .branch 170 ![2535301200456458802993406411137, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 324518553658426726783156020674576, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 679).pointIds 679), B3597, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3596 : B3596.tree = HexagonCover.NBand.M7300_7500.SplitData.node3596 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3597
  · rfl

def B3609 : Block := .branch 124 ![1267650600228229401496703205761, 1538, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 815).pointIds 815), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq3609 : B3609.tree = HexagonCover.NBand.M7300_7500.SplitData.node3609 := by
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
  · rfl

def B3608 : Block := .branch 100 ![385, 1461501637330902918204303802735925709793382106626, 6148, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![B3609, (.leaf 1 (Common.fact 941).pointIds 941), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 814).pointIds 814)]
theorem treeEq3608 : B3608.tree = HexagonCover.NBand.M7300_7500.SplitData.node3608 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3609
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3607 : Block := .branch 160 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 98320, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 285).pointIds 285), B3608, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq3607 : B3607.tree = HexagonCover.NBand.M7300_7500.SplitData.node3607 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3608
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3606 : Block := .branch 162 ![385, 618970019642690137449563650, 18446745173221185540, 24584, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605616950545057932291876585536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B3607, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq3606 : B3606.tree = HexagonCover.NBand.M7300_7500.SplitData.node3606 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3607
  · rfl
  · rfl
  · rfl

def B3605 : Block := .branch 171 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807459079547597433676942028570688] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B3606]
theorem treeEq3605 : B3605.tree = HexagonCover.NBand.M7300_7500.SplitData.node3605 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3606

def B3604 : Block := .branch 170 ![385, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 42535295865117307932921825928971419680, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3605, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3604 : B3604.tree = HexagonCover.NBand.M7300_7500.SplitData.node3604 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3605
  · rfl
  · rfl

def B3603 : Block := .branch 125 ![374144419156711147062678618375824911834912137412993, 618970019786805325525419522, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![(.leaf 0 (Common.fact 410).pointIds 410), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3604, (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3603 : B3603.tree = HexagonCover.NBand.M7300_7500.SplitData.node3603 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3604
  · rfl

def B3602 : Block := .branch 168 ![2535301200456458802993406411137, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071808409817497768605728064555974720] ![B3603, (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 480).pointIds 480)]
theorem treeEq3602 : B3602.tree = HexagonCover.NBand.M7300_7500.SplitData.node3602 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3603
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3595 : Block := .branch 108 ![2535301200456458802993406411137, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B3596, (.leaf 5 (Common.fact 308).pointIds 308), B3602]
theorem treeEq3595 : B3595.tree = HexagonCover.NBand.M7300_7500.SplitData.node3595 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3596
  · rfl
  · exact treeEq3602

theorem accepted3595 : B3595.accepted = true := by decide +kernel
theorem checked3595 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3595 (maskNeeds ![2535301200456458802993406411137, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq3595]
  exact B3595.sound accepted3595
#print axioms checked3595

def Tip3593_3595 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3595 ![2535301200456458802993406411137, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked3595
def B3617 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq3617 : B3617.tree = HexagonCover.NBand.M7300_7500.SplitData.node3617 := by
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

def B3616 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3617, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq3616 : B3616.tree = HexagonCover.NBand.M7300_7500.SplitData.node3616 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3617
  · rfl
  · rfl

def B3615 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3616]
theorem treeEq3615 : B3615.tree = HexagonCover.NBand.M7300_7500.SplitData.node3615 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3616

def B3614 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B3615, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3614 : B3614.tree = HexagonCover.NBand.M7300_7500.SplitData.node3614 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3615
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3613 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3614]
theorem treeEq3613 : B3613.tree = HexagonCover.NBand.M7300_7500.SplitData.node3613 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3614

def B3612 : Block := .branch 169 ![2475880078570760549798248833, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B3613, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq3612 : B3612.tree = HexagonCover.NBand.M7300_7500.SplitData.node3612 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3613
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3611 : Block := .branch 170 ![2475880078570760549798248833, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3612, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3611 : B3611.tree = HexagonCover.NBand.M7300_7500.SplitData.node3611 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3612
  · rfl

def B3610 : Block := .branch 171 ![2475880078570760549798248833, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071486426565039798337747901941809216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3611, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq3610 : B3610.tree = HexagonCover.NBand.M7300_7500.SplitData.node3610 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3611
  · rfl
  · rfl

def B3594 : Block := .branch 101 ![2475880078570760549798248833, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip3593_3595, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B3610]
theorem treeEq3594 : B3594.tree = HexagonCover.NBand.M7300_7500.SplitData.node3594 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3610

def B3625 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq3625 : B3625.tree = HexagonCover.NBand.M7300_7500.SplitData.node3625 := by
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

def B3624 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3625, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq3624 : B3624.tree = HexagonCover.NBand.M7300_7500.SplitData.node3624 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3625
  · rfl
  · rfl

def B3623 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3624]
theorem treeEq3623 : B3623.tree = HexagonCover.NBand.M7300_7500.SplitData.node3623 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3624

def B3622 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B3623, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3622 : B3622.tree = HexagonCover.NBand.M7300_7500.SplitData.node3622 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3623
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3621 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3622]
theorem treeEq3621 : B3621.tree = HexagonCover.NBand.M7300_7500.SplitData.node3621 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3622

def B3620 : Block := .branch 169 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B3621, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq3620 : B3620.tree = HexagonCover.NBand.M7300_7500.SplitData.node3620 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3621
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3619 : Block := .branch 170 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3620, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3619 : B3619.tree = HexagonCover.NBand.M7300_7500.SplitData.node3619 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3620
  · rfl

def B3618 : Block := .branch 171 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483893739719420449705458333646912] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3619, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq3618 : B3618.tree = HexagonCover.NBand.M7300_7500.SplitData.node3618 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3619
  · rfl
  · rfl

def B3593 : Block := .branch 91 ![385, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![B3594, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B3618]
theorem treeEq3593 : B3593.tree = HexagonCover.NBand.M7300_7500.SplitData.node3593 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3594
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3618

theorem accepted3593 : B3593.accepted = true := by decide +kernel
theorem checked3593 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3593 (maskNeeds ![385, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq3593]
  exact B3593.sound accepted3593
#print axioms checked3593

def Tip3591_3593 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3593 ![385, 619272251241849720307451394, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] checked3593
def B3633 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq3633 : B3633.tree = HexagonCover.NBand.M7300_7500.SplitData.node3633 := by
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

def B3632 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B3633, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq3632 : B3632.tree = HexagonCover.NBand.M7300_7500.SplitData.node3632 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3633
  · rfl
  · rfl

def B3631 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3632]
theorem treeEq3631 : B3631.tree = HexagonCover.NBand.M7300_7500.SplitData.node3631 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3632

def B3630 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B3631, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3630 : B3630.tree = HexagonCover.NBand.M7300_7500.SplitData.node3630 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3631
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3629 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3630]
theorem treeEq3629 : B3629.tree = HexagonCover.NBand.M7300_7500.SplitData.node3629 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3630

def B3628 : Block := .branch 169 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B3629, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq3628 : B3628.tree = HexagonCover.NBand.M7300_7500.SplitData.node3628 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3629
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3627 : Block := .branch 170 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3628, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3627 : B3627.tree = HexagonCover.NBand.M7300_7500.SplitData.node3627 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3628
  · rfl

def B3626 : Block := .branch 171 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891882809361521635045984960576] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3627, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq3626 : B3626.tree = HexagonCover.NBand.M7300_7500.SplitData.node3626 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3627
  · rfl
  · rfl

def B3592 : Block := .branch 89 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip3591_3593, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B3626]
theorem treeEq3592 : B3592.tree = HexagonCover.NBand.M7300_7500.SplitData.node3592 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3626

def B3641 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq3641 : B3641.tree = HexagonCover.NBand.M7300_7500.SplitData.node3641 := by
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

def B3640 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B3641, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq3640 : B3640.tree = HexagonCover.NBand.M7300_7500.SplitData.node3640 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3641
  · rfl
  · rfl

def B3639 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 997).pointIds 997), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3640]
theorem treeEq3639 : B3639.tree = HexagonCover.NBand.M7300_7500.SplitData.node3639 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3640

def B3638 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516473233940747894922285678656] ![B3639, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq3638 : B3638.tree = HexagonCover.NBand.M7300_7500.SplitData.node3638 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3639
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3637 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231455044394782033410, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3638]
theorem treeEq3637 : B3637.tree = HexagonCover.NBand.M7300_7500.SplitData.node3637 := by
  change Tree.branch (164 : Fin 172) _ = Tree.branch (164 : Fin 172) _
  apply congrArg (Tree.branch (164 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3638

def B3636 : Block := .branch 169 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B3637, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq3636 : B3636.tree = HexagonCover.NBand.M7300_7500.SplitData.node3636 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3637
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3635 : Block := .branch 170 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3636, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3635 : B3635.tree = HexagonCover.NBand.M7300_7500.SplitData.node3635 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3636
  · rfl

def B3634 : Block := .branch 171 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891341210594334281175716593728] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3635, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq3634 : B3634.tree = HexagonCover.NBand.M7300_7500.SplitData.node3634 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3635
  · rfl
  · rfl

def B3591 : Block := .branch 86 ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 939).pointIds 939), B3592, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B3634]
theorem treeEq3591 : B3591.tree = HexagonCover.NBand.M7300_7500.SplitData.node3591 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3592
  · rfl
  · rfl
  · exact treeEq3634

theorem accepted3591 : B3591.accepted = true := by decide +kernel
theorem checked3591 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3591 (maskNeeds ![385, 302231599159582857889282, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq3591]
  exact B3591.sound accepted3591
#print axioms checked3591

end HexagonCover.NBand.M7300_7500.SplitTree.Run0050
