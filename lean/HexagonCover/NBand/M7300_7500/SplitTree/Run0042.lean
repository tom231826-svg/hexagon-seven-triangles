import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0041
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0042
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2926_2929 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2929 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0041.checked2929
def B2988 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq2988 : B2988.tree = HexagonCover.NBand.M7300_7500.SplitData.node2988 := by
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

def B2987 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B2988, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq2987 : B2987.tree = HexagonCover.NBand.M7300_7500.SplitData.node2987 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2988
  · rfl
  · rfl

def B2986 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B2987, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq2986 : B2986.tree = HexagonCover.NBand.M7300_7500.SplitData.node2986 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2987
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2985 : Block := .branch 160 ![385, 302821822912347525613058, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 942).pointIds 942), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2986]
theorem treeEq2985 : B2985.tree = HexagonCover.NBand.M7300_7500.SplitData.node2985 := by
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
  · exact treeEq2986

def B2984 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231527101988819961346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B2985, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq2984 : B2984.tree = HexagonCover.NBand.M7300_7500.SplitData.node2984 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2985
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2983 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231527101988819961346, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2984]
theorem treeEq2983 : B2983.tree = HexagonCover.NBand.M7300_7500.SplitData.node2983 := by
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
  · exact treeEq2984

def B2982 : Block := .branch 169 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B2983, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2982 : B2982.tree = HexagonCover.NBand.M7300_7500.SplitData.node2982 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2983
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2981 : Block := .branch 170 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2982, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq2981 : B2981.tree = HexagonCover.NBand.M7300_7500.SplitData.node2981 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2982
  · rfl

def B2980 : Block := .branch 171 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891265048267698559537710104640] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B2981, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq2980 : B2980.tree = HexagonCover.NBand.M7300_7500.SplitData.node2980 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2981
  · rfl
  · rfl

def B2928 : Block := .branch 80 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![Tip2926_2929, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B2980]
theorem treeEq2928 : B2928.tree = HexagonCover.NBand.M7300_7500.SplitData.node2928 := by
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
  · exact treeEq2980

def B2927 : Block := .branch 149 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B2928, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 938).pointIds 938)]
theorem treeEq2927 : B2927.tree = HexagonCover.NBand.M7300_7500.SplitData.node2927 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2928
  · rfl
  · rfl

def B2926 : Block := .branch 88 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B2927]
theorem treeEq2926 : B2926.tree = HexagonCover.NBand.M7300_7500.SplitData.node2926 := by
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
  · exact treeEq2927

theorem accepted2926 : B2926.accepted = true := by decide +kernel
theorem checked2926 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2926 (maskNeeds ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954354332057599839810617408]) := by
  rw [← treeEq2926]
  exact B2926.sound accepted2926
#print axioms checked2926

def B3011 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275488515612336070444184981120785753571392] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 679).pointIds 679), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq3011 : B3011.tree = HexagonCover.NBand.M7300_7500.SplitData.node3011 := by
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

def B3010 : Block := .branch 124 ![10385861367669883486462489361645953, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 825).pointIds 825), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B3011]
theorem treeEq3010 : B3010.tree = HexagonCover.NBand.M7300_7500.SplitData.node3010 := by
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
  · exact treeEq3011

def B3009 : Block := .branch 100 ![10384593717069655257060992658440577, 1461501637330902918203684833011430924835285370370, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B3010, (.leaf 1 (Common.fact 946).pointIds 946), (.leaf 2 (Common.fact 433).pointIds 433), (.leaf 3 (Common.fact 434).pointIds 434), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq3009 : B3009.tree = HexagonCover.NBand.M7300_7500.SplitData.node3009 := by
  change Tree.branch (100 : Fin 172) _ = Tree.branch (100 : Fin 172) _
  apply congrArg (Tree.branch (100 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3010
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3008 : Block := .branch 160 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 285).pointIds 285), B3009, (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq3008 : B3008.tree = HexagonCover.NBand.M7300_7500.SplitData.node3008 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3009
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3007 : Block := .branch 75 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 5846006549323611672814778016491359746757320794120, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 660).pointIds 660), (.leaf 1 (Common.fact 661).pointIds 661), B3008, (.leaf 3 (Common.fact 662).pointIds 662), (.leaf 4 (Common.fact 663).pointIds 663), (.leaf 5 (Common.fact 664).pointIds 664), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq3007 : B3007.tree = HexagonCover.NBand.M7300_7500.SplitData.node3007 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3008
  · rfl
  · rfl
  · rfl
  · rfl

def B3006 : Block := .branch 162 ![10384593717069655257060992658440577, 295147905179352827394, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B3007, (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq3006 : B3006.tree = HexagonCover.NBand.M7300_7500.SplitData.node3006 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3007
  · rfl
  · rfl
  · rfl

def B3005 : Block := .branch 168 ![10384593717069655257060992658440577, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![B3006, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq3005 : B3005.tree = HexagonCover.NBand.M7300_7500.SplitData.node3005 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3006
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3004 : Block := .branch 171 ![10384593717069655257060992658440577, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B3005]
theorem treeEq3004 : B3004.tree = HexagonCover.NBand.M7300_7500.SplitData.node3004 := by
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
  · exact treeEq3005

def B3003 : Block := .branch 170 ![10384593717069655257060992658440577, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3004, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3003 : B3003.tree = HexagonCover.NBand.M7300_7500.SplitData.node3003 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3004
  · rfl
  · rfl

def B3002 : Block := .branch 169 ![10384593717070245552871351364092289, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), B3003, (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq3002 : B3002.tree = HexagonCover.NBand.M7300_7500.SplitData.node3002 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3003
  · rfl

theorem accepted3002 : B3002.accepted = true := by decide +kernel
theorem checked3002 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3002 (maskNeeds ![10384593717070245552871351364092289, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq3002]
  exact B3002.sound accepted3002
#print axioms checked3002

def Tip3001_3002 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3002 ![10384593717070245552871351364092289, 295364218698954966530, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] checked3002
def B3021 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq3021 : B3021.tree = HexagonCover.NBand.M7300_7500.SplitData.node3021 := by
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

def B3020 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B3021, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq3020 : B3020.tree = HexagonCover.NBand.M7300_7500.SplitData.node3020 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3021
  · rfl
  · rfl

def B3019 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3020]
theorem treeEq3019 : B3019.tree = HexagonCover.NBand.M7300_7500.SplitData.node3019 := by
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
  · exact treeEq3020

def B3018 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931710731424266966340730944] ![B3019, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq3018 : B3018.tree = HexagonCover.NBand.M7300_7500.SplitData.node3018 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3019
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3017 : Block := .branch 159 ![748288838313422294120289110230815476824387260252545, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 716).pointIds 716), (.leaf 1 (Common.fact 948).pointIds 948), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B3018]
theorem treeEq3017 : B3017.tree = HexagonCover.NBand.M7300_7500.SplitData.node3017 := by
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
  · exact treeEq3018

def B3016 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3017]
theorem treeEq3016 : B3016.tree = HexagonCover.NBand.M7300_7500.SplitData.node3016 := by
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
  · exact treeEq3017

def B3015 : Block := .branch 169 ![2475880078570760549798248833, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387270895952471420043328] ![B3016, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq3015 : B3015.tree = HexagonCover.NBand.M7300_7500.SplitData.node3015 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3016
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3014 : Block := .branch 170 ![2475880078570760549798248833, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3015, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3014 : B3014.tree = HexagonCover.NBand.M7300_7500.SplitData.node3014 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3015
  · rfl

def B3013 : Block := .branch 171 ![2475880078570760549798248833, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 1461501659108974402094639262606204345410066579520] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3014, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq3013 : B3013.tree = HexagonCover.NBand.M7300_7500.SplitData.node3013 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3014
  · rfl
  · rfl

def B3012 : Block := .branch 160 ![2475880078570760549798248833, 738086076467984205314, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 947).pointIds 947), (.leaf 2 (Common.fact 914).pointIds 914), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B3013]
theorem treeEq3012 : B3012.tree = HexagonCover.NBand.M7300_7500.SplitData.node3012 := by
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
  · exact treeEq3013

def B3001 : Block := .branch 69 ![10384596192949733827821542456689025, 442938171288631379458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![Tip3001_3002, B3012, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3001 : B3001.tree = HexagonCover.NBand.M7300_7500.SplitData.node3001 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3012
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3001 : B3001.accepted = true := by decide +kernel
theorem checked3001 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3001 (maskNeeds ![10384596192949733827821542456689025, 442938171288631379458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq3001]
  exact B3001.sound accepted3001
#print axioms checked3001

def Tip2997_3001 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node3001 ![10384596192949733827821542456689025, 442938171288631379458, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] checked3001
def B3030 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5316911983139663491615228241121476624, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 725).pointIds 725), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq3030 : B3030.tree = HexagonCover.NBand.M7300_7500.SplitData.node3030 := by
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

def B3029 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), B3030, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 724).pointIds 724)]
theorem treeEq3029 : B3029.tree = HexagonCover.NBand.M7300_7500.SplitData.node3029 := by
  change Tree.branch (122 : Fin 172) _ = Tree.branch (122 : Fin 172) _
  apply congrArg (Tree.branch (122 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3030
  · rfl
  · rfl

def B3028 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3029]
theorem treeEq3028 : B3028.tree = HexagonCover.NBand.M7300_7500.SplitData.node3028 := by
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
  · exact treeEq3029

def B3027 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931711026572172145693556800] ![B3028, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq3027 : B3027.tree = HexagonCover.NBand.M7300_7500.SplitData.node3027 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3028
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3026 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 723).pointIds 723), B3027, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3026 : B3026.tree = HexagonCover.NBand.M7300_7500.SplitData.node3026 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3027
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3025 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3026]
theorem treeEq3025 : B3025.tree = HexagonCover.NBand.M7300_7500.SplitData.node3025 := by
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
  · exact treeEq3026

def B3024 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![B3025, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq3024 : B3024.tree = HexagonCover.NBand.M7300_7500.SplitData.node3024 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3025
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3023 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B3024, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3023 : B3023.tree = HexagonCover.NBand.M7300_7500.SplitData.node3023 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3024
  · rfl

def B3022 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954430185069230933486862400] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3023, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq3022 : B3022.tree = HexagonCover.NBand.M7300_7500.SplitData.node3022 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3023
  · rfl
  · rfl

def B3000 : Block := .branch 68 ![10384596192949733827821542456689025, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2997_3001, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B3022]
theorem treeEq3000 : B3000.tree = HexagonCover.NBand.M7300_7500.SplitData.node3000 := by
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
  · exact treeEq3022

def B2999 : Block := .branch 91 ![10384593717069655257060992658440577, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B3000, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2999 : B2999.tree = HexagonCover.NBand.M7300_7500.SplitData.node2999 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3000
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2998 : Block := .branch 113 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![B2999, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2998 : B2998.tree = HexagonCover.NBand.M7300_7500.SplitData.node2998 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2997 : Block := .branch 149 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544] ![(.leaf 0 (Common.fact 70).pointIds 70), (.leaf 1 (Common.fact 71).pointIds 71), (.leaf 2 (Common.fact 72).pointIds 72), (.leaf 3 (Common.fact 73).pointIds 73), B2998, (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq2997 : B2997.tree = HexagonCover.NBand.M7300_7500.SplitData.node2997 := by
  change Tree.branch (149 : Fin 172) _ = Tree.branch (149 : Fin 172) _
  apply congrArg (Tree.branch (149 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2998
  · rfl
  · rfl

theorem accepted2997 : B2997.accepted = true := by decide +kernel
theorem checked2997 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2997 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483890954429889921325754134036544]) := by
  rw [← treeEq2997]
  exact B2997.sound accepted2997
#print axioms checked2997

def B3050 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 5923635443359696771970425166172221025124368, 393248, 2996078356550129053800811190865103043866287534506048] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 963).pointIds 963), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq3050 : B3050.tree = HexagonCover.NBand.M7300_7500.SplitData.node3050 := by
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

def B3049 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 1496577682550480031600270040671898978299895949131792, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 962).pointIds 962), (.leaf 5 (Common.fact 656).pointIds 656), B3050]
theorem treeEq3049 : B3049.tree = HexagonCover.NBand.M7300_7500.SplitData.node3049 := by
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
  · exact treeEq3050

def B3048 : Block := .branch 170 ![385, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972987002208454690542538204970878178295840, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), B3049, (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3048 : B3048.tree = HexagonCover.NBand.M7300_7500.SplitData.node3048 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3049
  · rfl
  · rfl

def B3047 : Block := .branch 125 ![374144419156711157444737034245023710092911389442433, 144115188075857410, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 960).pointIds 960), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B3048, (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3047 : B3047.tree = HexagonCover.NBand.M7300_7500.SplitData.node3047 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3048
  · rfl

def B3046 : Block := .branch 168 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 14615016395087100665928112166504709141467860828224] ![B3047, (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq3046 : B3046.tree = HexagonCover.NBand.M7300_7500.SplitData.node3046 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3047
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3045 : Block := .branch 163 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 233840261972944466912589573234605283144949207269408, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 959).pointIds 959), (.leaf 5 (Common.fact 248).pointIds 248), B3046]
theorem treeEq3045 : B3045.tree = HexagonCover.NBand.M7300_7500.SplitData.node3045 := by
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
  · exact treeEq3046

def B3044 : Block := .branch 165 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 187072209578355573530071658587684226515959365894176, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 958).pointIds 958), B3045, (.leaf 0 [] 0)]
theorem treeEq3044 : B3044.tree = HexagonCover.NBand.M7300_7500.SplitData.node3044 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3045
  · rfl

def B3043 : Block := .branch 167 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 5923635443359696771970425166172221025124368, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 957).pointIds 957), B3044, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq3043 : B3043.tree = HexagonCover.NBand.M7300_7500.SplitData.node3043 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3044
  · rfl

def B3042 : Block := .branch 142 ![10384593717069655257060992658440577, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298633504774444984220400484416] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B3043, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq3042 : B3042.tree = HexagonCover.NBand.M7300_7500.SplitData.node3042 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3043
  · rfl
  · rfl

def B3041 : Block := .branch 88 ![10384593717069655257060992658440577, 302231671217176895817218, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 393248, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 64).pointIds 64), (.leaf 1 (Common.fact 937).pointIds 937), (.leaf 2 (Common.fact 66).pointIds 66), (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), B3042]
theorem treeEq3041 : B3041.tree = HexagonCover.NBand.M7300_7500.SplitData.node3041 := by
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
  · exact treeEq3042

def B3058 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3058 : B3058.tree = HexagonCover.NBand.M7300_7500.SplitData.node3058 := by
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

def B3057 : Block := .branch 162 ![385, 1538, 6148, 18889465931478580879368, 98320, 393248, 400451448650445471071066618778206034515939907076160] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), B3058, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3057 : B3057.tree = HexagonCover.NBand.M7300_7500.SplitData.node3057 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3058
  · rfl
  · rfl

def B3056 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 393248, 26307029493734324010923301602837581484021176074304] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 932).pointIds 932), (.leaf 2 (Common.fact 933).pointIds 933), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 374).pointIds 374), B3057]
theorem treeEq3056 : B3056.tree = HexagonCover.NBand.M7300_7500.SplitData.node3056 := by
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
  · exact treeEq3057

def B3055 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 26307029493734324010923301602837581484021176074304] ![B3056, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 628).pointIds 628), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3055 : B3055.tree = HexagonCover.NBand.M7300_7500.SplitData.node3055 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3056
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3054 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B3055]
theorem treeEq3054 : B3054.tree = HexagonCover.NBand.M7300_7500.SplitData.node3054 := by
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
  · exact treeEq3055

def B3053 : Block := .branch 169 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 98320, 1496577676670400731206453392024785761878941255467040, 2923003296439877319664344279377053169526255386688] ![B3054, (.leaf 1 (Common.fact 921).pointIds 921), (.leaf 2 (Common.fact 922).pointIds 922), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 626).pointIds 626), (.leaf 6 (Common.fact 966).pointIds 966)]
theorem treeEq3053 : B3053.tree = HexagonCover.NBand.M7300_7500.SplitData.node3053 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq3054
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3052 : Block := .branch 170 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 2993155353602138320208187523989443222265480496644112, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 918).pointIds 918), (.leaf 2 (Common.fact 919).pointIds 919), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 965).pointIds 965), B3053, (.leaf 6 (Common.fact 920).pointIds 920)]
theorem treeEq3052 : B3052.tree = HexagonCover.NBand.M7300_7500.SplitData.node3052 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3053
  · rfl

def B3051 : Block := .branch 171 ![2475880078570760549798248833, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324321996078542808969379904] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 915).pointIds 915), (.leaf 2 (Common.fact 916).pointIds 916), (.leaf 3 (Common.fact 620).pointIds 620), B3052, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3051 : B3051.tree = HexagonCover.NBand.M7300_7500.SplitData.node3051 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3052
  · rfl
  · rfl

def B3040 : Block := .branch 78 ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360] ![(.leaf 0 (Common.fact 134).pointIds 134), B3041, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B3051]
theorem treeEq3040 : B3040.tree = HexagonCover.NBand.M7300_7500.SplitData.node3040 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3041
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3051

theorem accepted3040 : B3040.accepted = true := by decide +kernel
theorem checked3040 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node3040 (maskNeeds ![10384596192949733827821542456689025, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 348449143727040986586495598010130648629264, 43556142965880123323311949751266331459616, 2923003296439877320298324019764623639151675703360]) := by
  rw [← treeEq3040]
  exact B3040.sound accepted3040
#print axioms checked3040

end HexagonCover.NBand.M7300_7500.SplitTree.Run0042
