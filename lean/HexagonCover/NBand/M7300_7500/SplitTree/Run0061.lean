import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0060
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0061
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip4340_4341 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4341 ![10384593717070245552871351364092289, 295364077961466611202, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] HexagonCover.NBand.M7300_7500.SplitTree.Run0060.checked4341
def B4360 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq4360 : B4360.tree = HexagonCover.NBand.M7300_7500.SplitData.node4360 := by
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
  · rfl

def B4359 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B4360, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq4359 : B4359.tree = HexagonCover.NBand.M7300_7500.SplitData.node4359 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4360
  · rfl
  · rfl

def B4358 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4359]
theorem treeEq4358 : B4358.tree = HexagonCover.NBand.M7300_7500.SplitData.node4358 := by
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
  · exact treeEq4359

def B4357 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931710731424266966340730944] ![B4358, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq4357 : B4357.tree = HexagonCover.NBand.M7300_7500.SplitData.node4357 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4358
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4356 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 1015).pointIds 1015), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B4357]
theorem treeEq4356 : B4356.tree = HexagonCover.NBand.M7300_7500.SplitData.node4356 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4357

def B4355 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4356]
theorem treeEq4355 : B4355.tree = HexagonCover.NBand.M7300_7500.SplitData.node4355 := by
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
  · exact treeEq4356

def B4354 : Block := .branch 169 ![2475880078570760549798248833, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387270895952471420043328] ![B4355, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq4354 : B4354.tree = HexagonCover.NBand.M7300_7500.SplitData.node4354 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4355
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4353 : Block := .branch 170 ![2475880078570760549798248833, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4354, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4353 : B4353.tree = HexagonCover.NBand.M7300_7500.SplitData.node4353 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4354
  · rfl

def B4352 : Block := .branch 171 ![2475880078570760549798248833, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1461501659108974402094639262606204345410066579520] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4353, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq4352 : B4352.tree = HexagonCover.NBand.M7300_7500.SplitData.node4352 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4353
  · rfl
  · rfl

def B4351 : Block := .branch 160 ![2475880078570760549798248833, 738085935730495849986, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1014).pointIds 1014), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B4352]
theorem treeEq4351 : B4351.tree = HexagonCover.NBand.M7300_7500.SplitData.node4351 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4352

def B4340 : Block := .branch 69 ![10384596192949733827821542456689025, 442938030551143024130, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![Tip4340_4341, B4351, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4340 : B4340.tree = HexagonCover.NBand.M7300_7500.SplitData.node4340 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4351
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted4340 : B4340.accepted = true := by decide +kernel
theorem checked4340 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4340 (maskNeeds ![10384596192949733827821542456689025, 442938030551143024130, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq4340]
  exact B4340.sound accepted4340
#print axioms checked4340

def Tip4336_4340 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4340 ![10384596192949733827821542456689025, 442938030551143024130, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] checked4340
def B4369 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5316911983139663491615228241121476624, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 725).pointIds 725), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq4369 : B4369.tree = HexagonCover.NBand.M7300_7500.SplitData.node4369 := by
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

def B4368 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), B4369, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq4368 : B4368.tree = HexagonCover.NBand.M7300_7500.SplitData.node4368 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4369
  · rfl
  · rfl

def B4367 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4368]
theorem treeEq4367 : B4367.tree = HexagonCover.NBand.M7300_7500.SplitData.node4367 := by
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
  · exact treeEq4368

def B4366 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931711026572172145693556800] ![B4367, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq4366 : B4366.tree = HexagonCover.NBand.M7300_7500.SplitData.node4366 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4367
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4365 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 723).pointIds 723), B4366, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4365 : B4365.tree = HexagonCover.NBand.M7300_7500.SplitData.node4365 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4366
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4364 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4365]
theorem treeEq4364 : B4364.tree = HexagonCover.NBand.M7300_7500.SplitData.node4364 := by
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
  · exact treeEq4365

def B4363 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![B4364, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq4363 : B4363.tree = HexagonCover.NBand.M7300_7500.SplitData.node4363 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4364
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4362 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B4363, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4362 : B4362.tree = HexagonCover.NBand.M7300_7500.SplitData.node4362 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4363
  · rfl

def B4361 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4362, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq4361 : B4361.tree = HexagonCover.NBand.M7300_7500.SplitData.node4361 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4362
  · rfl
  · rfl

def B4339 : Block := .branch 68 ![10384596192949733827821542456689025, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip4336_4340, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B4361]
theorem treeEq4339 : B4339.tree = HexagonCover.NBand.M7300_7500.SplitData.node4339 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4361

def B4338 : Block := .branch 91 ![10384593717069655257060992658440577, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B4339, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4338 : B4338.tree = HexagonCover.NBand.M7300_7500.SplitData.node4338 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4339
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4337 : Block := .branch 113 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B4338, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4337 : B4337.tree = HexagonCover.NBand.M7300_7500.SplitData.node4337 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4338
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4336 : Block := .branch 149 ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B4337, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq4336 : B4336.tree = HexagonCover.NBand.M7300_7500.SplitData.node4336 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4337
  · rfl
  · rfl

theorem accepted4336 : B4336.accepted = true := by decide +kernel
theorem checked4336 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4336 (maskNeeds ![385, 147790125371790198274, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq4336]
  exact B4336.sound accepted4336
#print axioms checked4336

def B4389 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq4389 : B4389.tree = HexagonCover.NBand.M7300_7500.SplitData.node4389 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4388 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4389]
theorem treeEq4388 : B4388.tree = HexagonCover.NBand.M7300_7500.SplitData.node4388 := by
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
  · exact treeEq4389

def B4387 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4388, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4387 : B4387.tree = HexagonCover.NBand.M7300_7500.SplitData.node4387 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4388
  · rfl
  · rfl

def B4386 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4387, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq4386 : B4386.tree = HexagonCover.NBand.M7300_7500.SplitData.node4386 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4387
  · rfl

def B4385 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B4386, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq4385 : B4385.tree = HexagonCover.NBand.M7300_7500.SplitData.node4385 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4386
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4384 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4385]
theorem treeEq4384 : B4384.tree = HexagonCover.NBand.M7300_7500.SplitData.node4384 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4385

def B4383 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4384, (.leaf 0 [] 0)]
theorem treeEq4383 : B4383.tree = HexagonCover.NBand.M7300_7500.SplitData.node4383 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4384
  · rfl

def B4382 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4383, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4382 : B4382.tree = HexagonCover.NBand.M7300_7500.SplitData.node4382 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4383
  · rfl

def B4381 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4382, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq4381 : B4381.tree = HexagonCover.NBand.M7300_7500.SplitData.node4381 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4382
  · rfl
  · rfl

def B4380 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671076439407461890, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1012).pointIds 1012), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4381]
theorem treeEq4380 : B4380.tree = HexagonCover.NBand.M7300_7500.SplitData.node4380 := by
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
  · exact treeEq4381

def B4397 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq4397 : B4397.tree = HexagonCover.NBand.M7300_7500.SplitData.node4397 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4396 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), B4397, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq4396 : B4396.tree = HexagonCover.NBand.M7300_7500.SplitData.node4396 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4397
  · rfl
  · rfl

def B4395 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4396]
theorem treeEq4395 : B4395.tree = HexagonCover.NBand.M7300_7500.SplitData.node4395 := by
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
  · exact treeEq4396

def B4394 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B4395, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq4394 : B4394.tree = HexagonCover.NBand.M7300_7500.SplitData.node4394 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4395
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4393 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4394]
theorem treeEq4393 : B4393.tree = HexagonCover.NBand.M7300_7500.SplitData.node4393 := by
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
  · exact treeEq4394

def B4392 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B4393, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq4392 : B4392.tree = HexagonCover.NBand.M7300_7500.SplitData.node4392 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4393
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4391 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4392, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4391 : B4391.tree = HexagonCover.NBand.M7300_7500.SplitData.node4391 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4392
  · rfl

def B4390 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4391, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq4390 : B4390.tree = HexagonCover.NBand.M7300_7500.SplitData.node4390 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4391
  · rfl
  · rfl

def B4379 : Block := .branch 78 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B4380, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B4390]
theorem treeEq4379 : B4379.tree = HexagonCover.NBand.M7300_7500.SplitData.node4379 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4380
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4390

theorem accepted4379 : B4379.accepted = true := by decide +kernel
theorem checked4379 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4379 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4379]
  exact B4379.sound accepted4379
#print axioms checked4379

def Tip4377_4379 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4379 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] checked4379
def B4406 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800810881455651086247133133144128] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 973).pointIds 973)]
theorem treeEq4406 : B4406.tree = HexagonCover.NBand.M7300_7500.SplitData.node4406 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4405 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B4406]
theorem treeEq4405 : B4405.tree = HexagonCover.NBand.M7300_7500.SplitData.node4405 := by
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
  · exact treeEq4406

def B4404 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B4405, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4404 : B4404.tree = HexagonCover.NBand.M7300_7500.SplitData.node4404 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4405
  · rfl
  · rfl

def B4403 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B4404, (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq4403 : B4403.tree = HexagonCover.NBand.M7300_7500.SplitData.node4403 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4404
  · rfl

def B4402 : Block := .branch 168 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665927802757052751522313459466304] ![B4403, (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq4402 : B4402.tree = HexagonCover.NBand.M7300_7500.SplitData.node4402 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4403
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4401 : Block := .branch 163 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B4402]
theorem treeEq4401 : B4401.tree = HexagonCover.NBand.M7300_7500.SplitData.node4401 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4402

def B4400 : Block := .branch 165 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B4401, (.leaf 0 [] 0)]
theorem treeEq4400 : B4400.tree = HexagonCover.NBand.M7300_7500.SplitData.node4400 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4401
  · rfl

def B4399 : Block := .branch 167 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B4400, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq4399 : B4399.tree = HexagonCover.NBand.M7300_7500.SplitData.node4399 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4400
  · rfl

def B4398 : Block := .branch 142 ![10384593717069655257060992658440577, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B4399, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq4398 : B4398.tree = HexagonCover.NBand.M7300_7500.SplitData.node4398 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4399
  · rfl
  · rfl

def B4378 : Block := .branch 76 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip4377_4379, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B4398]
theorem treeEq4378 : B4378.tree = HexagonCover.NBand.M7300_7500.SplitData.node4378 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4398

def B4415 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 979).pointIds 979)]
theorem treeEq4415 : B4415.tree = HexagonCover.NBand.M7300_7500.SplitData.node4415 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4414 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 400451448650445471071066618476269727517461966225472] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), B4415, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 978).pointIds 978)]
theorem treeEq4414 : B4414.tree = HexagonCover.NBand.M7300_7500.SplitData.node4414 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4415
  · rfl
  · rfl

def B4413 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 393248, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 1011).pointIds 1011), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B4414]
theorem treeEq4413 : B4413.tree = HexagonCover.NBand.M7300_7500.SplitData.node4413 := by
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
  · exact treeEq4414

def B4412 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![B4413, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq4412 : B4412.tree = HexagonCover.NBand.M7300_7500.SplitData.node4412 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4413
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4411 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301300901274485543235223616] ![(.leaf 0 (Common.fact 723).pointIds 723), B4412, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq4411 : B4411.tree = HexagonCover.NBand.M7300_7500.SplitData.node4411 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4412
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4410 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B4411]
theorem treeEq4410 : B4410.tree = HexagonCover.NBand.M7300_7500.SplitData.node4410 := by
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
  · exact treeEq4411

def B4409 : Block := .branch 169 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664343977440746171048314536000] ![B4410, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 975).pointIds 975)]
theorem treeEq4409 : B4409.tree = HexagonCover.NBand.M7300_7500.SplitData.node4409 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq4410
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B4408 : Block := .branch 170 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B4409, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq4408 : B4408.tree = HexagonCover.NBand.M7300_7500.SplitData.node4408 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4409
  · rfl

def B4407 : Block := .branch 171 ![2475880078570760549798248833, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324020059771544331028529216] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B4408, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 974).pointIds 974)]
theorem treeEq4407 : B4407.tree = HexagonCover.NBand.M7300_7500.SplitData.node4407 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4408
  · rfl
  · rfl

def B4377 : Block := .branch 68 ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 637).pointIds 637), B4378, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B4407]
theorem treeEq4377 : B4377.tree = HexagonCover.NBand.M7300_7500.SplitData.node4377 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq4378
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4407

theorem accepted4377 : B4377.accepted = true := by decide +kernel
theorem checked4377 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4377 (maskNeeds ![10384596192949733827821542456689025, 216172782113785346, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq4377]
  exact B4377.sound accepted4377
#print axioms checked4377

end HexagonCover.NBand.M7300_7500.SplitTree.Run0061
