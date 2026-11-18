import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0069
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0070
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip4927_4930 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node4930 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0069.checked4930
def B5011 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq5011 : B5011.tree = HexagonCover.NBand.M7300_7500.SplitData.node5011 := by
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

def B5010 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B5011, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq5010 : B5010.tree = HexagonCover.NBand.M7300_7500.SplitData.node5010 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5011
  · rfl
  · rfl

def B5009 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B5010, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq5009 : B5009.tree = HexagonCover.NBand.M7300_7500.SplitData.node5009 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5008 : Block := .branch 160 ![385, 302821750714015999329794, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1018).pointIds 1018), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B5009]
theorem treeEq5008 : B5008.tree = HexagonCover.NBand.M7300_7500.SplitData.node5008 := by
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
  · exact treeEq5009

def B5007 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B5008, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq5007 : B5007.tree = HexagonCover.NBand.M7300_7500.SplitData.node5007 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5008
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5006 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454903657293678082, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5007]
theorem treeEq5006 : B5006.tree = HexagonCover.NBand.M7300_7500.SplitData.node5006 := by
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
  · exact treeEq5007

def B5005 : Block := .branch 169 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B5006, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq5005 : B5005.tree = HexagonCover.NBand.M7300_7500.SplitData.node5005 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5006
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5004 : Block := .branch 170 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5005, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5004 : B5004.tree = HexagonCover.NBand.M7300_7500.SplitData.node5004 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5005
  · rfl

def B5003 : Block := .branch 171 ![385, 302231599018845369533954, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5004, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq5003 : B5003.tree = HexagonCover.NBand.M7300_7500.SplitData.node5003 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5004
  · rfl
  · rfl

def B4929 : Block := .branch 80 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip4927_4930, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B5003]
theorem treeEq4929 : B4929.tree = HexagonCover.NBand.M7300_7500.SplitData.node4929 := by
  change Tree.branch (80 : Fin 172) _ = Tree.branch (80 : Fin 172) _
  apply congrArg (Tree.branch (80 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5003

def B4928 : Block := .branch 149 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B4929, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq4928 : B4928.tree = HexagonCover.NBand.M7300_7500.SplitData.node4928 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4929
  · rfl
  · rfl

def B4927 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B4928]
theorem treeEq4927 : B4927.tree = HexagonCover.NBand.M7300_7500.SplitData.node4927 := by
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
  · exact treeEq4928

theorem accepted4927 : B4927.accepted = true := by decide +kernel
theorem checked4927 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node4927 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 79266848140492005727134572552, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq4927]
  exact B4927.sound accepted4927
#print axioms checked4927

def B5034 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq5034 : B5034.tree = HexagonCover.NBand.M7300_7500.SplitData.node5034 := by
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

def B5033 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B5034]
theorem treeEq5033 : B5033.tree = HexagonCover.NBand.M7300_7500.SplitData.node5033 := by
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
  · exact treeEq5034

def B5032 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430924835285370370, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B5033, (.leaf 1 (Common.fact 946).pointIds 946), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq5032 : B5032.tree = HexagonCover.NBand.M7300_7500.SplitData.node5032 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5033
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5031 : Block := .branch 168 ![10384593717069655257060992658440577, 1461501637330902918203684833011430924835285370370, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B5032, (.leaf 1 (Common.fact 999).pointIds 999), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq5031 : B5031.tree = HexagonCover.NBand.M7300_7500.SplitData.node5031 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5032
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5030 : Block := .branch 160 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B5031, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq5030 : B5030.tree = HexagonCover.NBand.M7300_7500.SplitData.node5030 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5031
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5029 : Block := .branch 75 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B5030, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq5029 : B5029.tree = HexagonCover.NBand.M7300_7500.SplitData.node5029 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq5030
  · rfl
  · rfl
  · rfl
  · rfl

def B5028 : Block := .branch 162 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B5029, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq5028 : B5028.tree = HexagonCover.NBand.M7300_7500.SplitData.node5028 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq5029
  · rfl
  · rfl
  · rfl

def B5027 : Block := .branch 171 ![10384593717069655257060992658440577, 295292020367428683266, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B5028]
theorem treeEq5027 : B5027.tree = HexagonCover.NBand.M7300_7500.SplitData.node5027 := by
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
  · exact treeEq5028

def B5026 : Block := .branch 170 ![10384593717069655257060992658440577, 295292020367428683266, 18446745173221185540, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B5027, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5026 : B5026.tree = HexagonCover.NBand.M7300_7500.SplitData.node5026 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5027
  · rfl
  · rfl

def B5025 : Block := .branch 169 ![10384593717070245552871351364092289, 295292020367428683266, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), B5026, (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq5025 : B5025.tree = HexagonCover.NBand.M7300_7500.SplitData.node5025 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5026
  · rfl

theorem accepted5025 : B5025.accepted = true := by decide +kernel
theorem checked5025 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5025 (maskNeeds ![10384593717070245552871351364092289, 295292020367428683266, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq5025]
  exact B5025.sound accepted5025
#print axioms checked5025

def Tip5024_5025 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5025 ![10384593717070245552871351364092289, 295292020367428683266, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] checked5025
def B5044 : Block := .branch 142 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 895).pointIds 895), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 896).pointIds 896)]
theorem treeEq5044 : B5044.tree = HexagonCover.NBand.M7300_7500.SplitData.node5044 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5043 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5044, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5043 : B5043.tree = HexagonCover.NBand.M7300_7500.SplitData.node5043 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5044
  · rfl
  · rfl

def B5042 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B5043, (.leaf 6 (Common.fact 894).pointIds 894)]
theorem treeEq5042 : B5042.tree = HexagonCover.NBand.M7300_7500.SplitData.node5042 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5043
  · rfl

def B5041 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![B5042, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq5041 : B5041.tree = HexagonCover.NBand.M7300_7500.SplitData.node5041 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5042
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5040 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 737869762948382066178, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 1023).pointIds 1023), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B5041]
theorem treeEq5040 : B5040.tree = HexagonCover.NBand.M7300_7500.SplitData.node5040 := by
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
  · exact treeEq5041

def B5039 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 737869762948382066178, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5040]
theorem treeEq5039 : B5039.tree = HexagonCover.NBand.M7300_7500.SplitData.node5039 := by
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
  · exact treeEq5040

def B5038 : Block := .branch 169 ![2475880078570760549798248833, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 1461501659108974401460659219987178972127352586304] ![B5039, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq5038 : B5038.tree = HexagonCover.NBand.M7300_7500.SplitData.node5038 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5039
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5037 : Block := .branch 170 ![2475880078570760549798248833, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 1461501659108974402094639262606204345410066579520] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5038, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5037 : B5037.tree = HexagonCover.NBand.M7300_7500.SplitData.node5037 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5038
  · rfl

def B5036 : Block := .branch 171 ![2475880078570760549798248833, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1461501659108974402094639262606204345410066579520] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5037, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq5036 : B5036.tree = HexagonCover.NBand.M7300_7500.SplitData.node5036 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5037
  · rfl
  · rfl

def B5035 : Block := .branch 160 ![2475880078570760549798248833, 738013878136457922050, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 1022).pointIds 1022), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B5036]
theorem treeEq5035 : B5035.tree = HexagonCover.NBand.M7300_7500.SplitData.node5035 := by
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
  · exact treeEq5036

def B5024 : Block := .branch 69 ![10384596192949733827821542456689025, 442865972957105096194, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![Tip5024_5025, B5035, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5024 : B5024.tree = HexagonCover.NBand.M7300_7500.SplitData.node5024 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5035
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted5024 : B5024.accepted = true := by decide +kernel
theorem checked5024 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5024 (maskNeeds ![10384596192949733827821542456689025, 442865972957105096194, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq5024]
  exact B5024.sound accepted5024
#print axioms checked5024

def Tip5020_5024 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node5024 ![10384596192949733827821542456689025, 442865972957105096194, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] checked5024
def B5053 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 898).pointIds 898), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 899).pointIds 899)]
theorem treeEq5053 : B5053.tree = HexagonCover.NBand.M7300_7500.SplitData.node5053 := by
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

def B5052 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B5053, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq5052 : B5052.tree = HexagonCover.NBand.M7300_7500.SplitData.node5052 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5053
  · rfl
  · rfl

def B5051 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B5052, (.leaf 6 (Common.fact 897).pointIds 897)]
theorem treeEq5051 : B5051.tree = HexagonCover.NBand.M7300_7500.SplitData.node5051 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5052
  · rfl

def B5050 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![B5051, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq5050 : B5050.tree = HexagonCover.NBand.M7300_7500.SplitData.node5050 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5051
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5049 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 723).pointIds 723), B5050, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq5049 : B5049.tree = HexagonCover.NBand.M7300_7500.SplitData.node5049 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5050
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5048 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B5049]
theorem treeEq5048 : B5048.tree = HexagonCover.NBand.M7300_7500.SplitData.node5048 := by
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
  · exact treeEq5049

def B5047 : Block := .branch 169 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![B5048, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq5047 : B5047.tree = HexagonCover.NBand.M7300_7500.SplitData.node5047 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5048
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5046 : Block := .branch 170 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B5047, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5046 : B5046.tree = HexagonCover.NBand.M7300_7500.SplitData.node5046 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5047
  · rfl

def B5045 : Block := .branch 171 ![2475880078570760549798248833, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5046, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq5045 : B5045.tree = HexagonCover.NBand.M7300_7500.SplitData.node5045 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5046
  · rfl
  · rfl

def B5023 : Block := .branch 68 ![10384596192949733827821542456689025, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip5020_5024, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B5045]
theorem treeEq5023 : B5023.tree = HexagonCover.NBand.M7300_7500.SplitData.node5023 := by
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
  · exact treeEq5045

def B5022 : Block := .branch 91 ![10384593717069655257060992658440577, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B5023, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq5022 : B5022.tree = HexagonCover.NBand.M7300_7500.SplitData.node5022 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5023
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5021 : Block := .branch 113 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B5022, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq5021 : B5021.tree = HexagonCover.NBand.M7300_7500.SplitData.node5021 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5022
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5020 : Block := .branch 149 ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B5021, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq5020 : B5020.tree = HexagonCover.NBand.M7300_7500.SplitData.node5020 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5021
  · rfl
  · rfl

theorem accepted5020 : B5020.accepted = true := by decide +kernel
theorem checked5020 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5020 (maskNeeds ![385, 147718067777752270338, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq5020]
  exact B5020.sound accepted5020
#print axioms checked5020

def B5076 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq5076 : B5076.tree = HexagonCover.NBand.M7300_7500.SplitData.node5076 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5075 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5076, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq5075 : B5075.tree = HexagonCover.NBand.M7300_7500.SplitData.node5075 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5076
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5074 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B5075, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq5074 : B5074.tree = HexagonCover.NBand.M7300_7500.SplitData.node5074 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5075
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5073 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665294132123885683768185146835008] ![B5074, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq5073 : B5073.tree = HexagonCover.NBand.M7300_7500.SplitData.node5073 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5074
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5072 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5073, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5072 : B5072.tree = HexagonCover.NBand.M7300_7500.SplitData.node5072 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5073
  · rfl

def B5071 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742851497369841220091591000128] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5072, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq5071 : B5071.tree = HexagonCover.NBand.M7300_7500.SplitData.node5071 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5072
  · rfl
  · rfl

def B5070 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5071]
theorem treeEq5070 : B5070.tree = HexagonCover.NBand.M7300_7500.SplitData.node5070 := by
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
  · exact treeEq5071

def B5069 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665928112166504709141467860828224] ![B5070, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq5069 : B5069.tree = HexagonCover.NBand.M7300_7500.SplitData.node5069 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5070
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5068 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5069]
theorem treeEq5068 : B5068.tree = HexagonCover.NBand.M7300_7500.SplitData.node5068 := by
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
  · exact treeEq5069

def B5067 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5068, (.leaf 0 [] 0)]
theorem treeEq5067 : B5067.tree = HexagonCover.NBand.M7300_7500.SplitData.node5067 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5068
  · rfl

def B5066 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5067, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5066 : B5066.tree = HexagonCover.NBand.M7300_7500.SplitData.node5066 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5067
  · rfl

def B5065 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5066, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq5065 : B5065.tree = HexagonCover.NBand.M7300_7500.SplitData.node5065 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5066
  · rfl
  · rfl

def B5064 : Block := .branch 88 ![385, 302231599018845369533954, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 1016).pointIds 1016), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B5065]
theorem treeEq5064 : B5064.tree = HexagonCover.NBand.M7300_7500.SplitData.node5064 := by
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
  · exact treeEq5065

theorem accepted5064 : B5064.accepted = true := by decide +kernel
theorem checked5064 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5064 (maskNeeds ![385, 302231599018845369533954, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq5064]
  exact B5064.sound accepted5064
#print axioms checked5064

def B5097 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938643345198119042965259391045023890462343200, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 1027).pointIds 1027), (.leaf 6 (Common.fact 972).pointIds 972)]
theorem treeEq5097 : B5097.tree = HexagonCover.NBand.M7300_7500.SplitData.node5097 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5096 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285380274899125762, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5097, (.leaf 1 (Common.fact 1026).pointIds 1026), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq5096 : B5096.tree = HexagonCover.NBand.M7300_7500.SplitData.node5096 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5097
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5095 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1538, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![(.leaf 0 (Common.fact 906).pointIds 906), B5096, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq5095 : B5095.tree = HexagonCover.NBand.M7300_7500.SplitData.node5095 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5096
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5094 : Block := .branch 169 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 1730417938643345198119042965259391045023890462343200, 14615016395087100665293822714433726149030745473088] ![B5095, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 1024).pointIds 1024), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq5094 : B5094.tree = HexagonCover.NBand.M7300_7500.SplitData.node5094 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5095
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5093 : Block := .branch 170 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155359177324619840843309373372790427570873139216, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 962).pointIds 962), B5094, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq5093 : B5093.tree = HexagonCover.NBand.M7300_7500.SplitData.node5093 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5094
  · rfl

def B5092 : Block := .branch 171 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 20461022944410712338742542087917883600937189638208] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B5093, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq5092 : B5092.tree = HexagonCover.NBand.M7300_7500.SplitData.node5092 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5093
  · rfl
  · rfl

def B5091 : Block := .branch 162 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), B5092]
theorem treeEq5091 : B5091.tree = HexagonCover.NBand.M7300_7500.SplitData.node5091 := by
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
  · exact treeEq5092

def B5090 : Block := .branch 78 ![5192296858534827628530496329220481, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![(.leaf 0 (Common.fact 134).pointIds 134), B5091, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 1008).pointIds 1008)]
theorem treeEq5090 : B5090.tree = HexagonCover.NBand.M7300_7500.SplitData.node5090 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq5091
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5089 : Block := .branch 112 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 14615016395087100665927802757052751522313459466304] ![B5090, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 1007).pointIds 1007)]
theorem treeEq5089 : B5089.tree = HexagonCover.NBand.M7300_7500.SplitData.node5089 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq5090
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B5088 : Block := .branch 163 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840262016500609878469696557917232896215538335776, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B5089]
theorem treeEq5088 : B5088.tree = HexagonCover.NBand.M7300_7500.SplitData.node5088 := by
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
  · exact treeEq5089

def B5087 : Block := .branch 165 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209621911716495951781910996176267225696960544, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B5088, (.leaf 0 [] 0)]
theorem treeEq5087 : B5087.tree = HexagonCover.NBand.M7300_7500.SplitData.node5087 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5088
  · rfl

def B5086 : Block := .branch 167 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B5087, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq5086 : B5086.tree = HexagonCover.NBand.M7300_7500.SplitData.node5086 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5087
  · rfl

def B5085 : Block := .branch 142 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B5086, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq5085 : B5085.tree = HexagonCover.NBand.M7300_7500.SplitData.node5085 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq5086
  · rfl
  · rfl

theorem accepted5085 : B5085.accepted = true := by decide +kernel
theorem checked5085 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node5085 (maskNeeds ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324095322487365065999122496]) := by
  rw [← treeEq5085]
  exact B5085.sound accepted5085
#print axioms checked5085

end HexagonCover.NBand.M7300_7500.SplitTree.Run0070
