import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0035
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0036
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2641_2644 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2644 ![10387129018270111715863986064851329, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0035.checked2644
def B2666 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq2666 : B2666.tree = HexagonCover.NBand.M6900_7100.SplitData.node2666 := by
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

def B2665 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2666, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq2665 : B2665.tree = HexagonCover.NBand.M6900_7100.SplitData.node2665 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2666
  · rfl
  · rfl

def B2664 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2665, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2664 : B2664.tree = HexagonCover.NBand.M6900_7100.SplitData.node2664 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2665
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2663 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2664]
theorem treeEq2663 : B2663.tree = HexagonCover.NBand.M6900_7100.SplitData.node2663 := by
  change Tree.branch (164 : Fin 173) _ = Tree.branch (164 : Fin 173) _
  apply congrArg (Tree.branch (164 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2664

def B2662 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2663]
theorem treeEq2662 : B2662.tree = HexagonCover.NBand.M6900_7100.SplitData.node2662 := by
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
  · exact treeEq2663

def B2661 : Block := .branch 171 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2662, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1059).pointIds 1059)]
theorem treeEq2661 : B2661.tree = HexagonCover.NBand.M6900_7100.SplitData.node2661 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2662
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2660 : Block := .branch 151 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2661, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2660 : B2660.tree = HexagonCover.NBand.M6900_7100.SplitData.node2660 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2661
  · rfl

def B2659 : Block := .branch 170 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2660, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq2659 : B2659.tree = HexagonCover.NBand.M6900_7100.SplitData.node2659 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2660
  · rfl
  · rfl

def B2643 : Block := .branch 101 ![10384596192949733827821542456689025, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip2641_2644, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2659]
theorem treeEq2643 : B2643.tree = HexagonCover.NBand.M6900_7100.SplitData.node2643 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2659

def B2668 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1062).pointIds 1062)]
theorem treeEq2668 : B2668.tree = HexagonCover.NBand.M6900_7100.SplitData.node2668 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2667 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2668, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1061).pointIds 1061)]
theorem treeEq2667 : B2667.tree = HexagonCover.NBand.M6900_7100.SplitData.node2667 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2668
  · rfl
  · rfl
  · rfl

def B2642 : Block := .branch 91 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2643, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2667]
theorem treeEq2642 : B2642.tree = HexagonCover.NBand.M6900_7100.SplitData.node2642 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2643
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2667

def B2674 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1122433257491911512663687080580323301994847652020288] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 1137).pointIds 1137)]
theorem treeEq2674 : B2674.tree = HexagonCover.NBand.M6900_7100.SplitData.node2674 := by
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

def B2673 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080580323301994847652020288] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2674, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 1136).pointIds 1136)]
theorem treeEq2673 : B2673.tree = HexagonCover.NBand.M6900_7100.SplitData.node2673 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2674
  · rfl
  · rfl

def B2672 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229586395931010190016576] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2673]
theorem treeEq2672 : B2672.tree = HexagonCover.NBand.M6900_7100.SplitData.node2672 := by
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
  · exact treeEq2673

def B2671 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543401065199606038621147639578688] ![B2672, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1063).pointIds 1063)]
theorem treeEq2671 : B2671.tree = HexagonCover.NBand.M6900_7100.SplitData.node2671 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2672
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2670 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2671, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2670 : B2670.tree = HexagonCover.NBand.M6900_7100.SplitData.node2670 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2671
  · rfl

def B2669 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374684615859966216364359744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2670, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 731).pointIds 731)]
theorem treeEq2669 : B2669.tree = HexagonCover.NBand.M6900_7100.SplitData.node2669 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2670
  · rfl
  · rfl

def B2641 : Block := .branch 89 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 104).pointIds 104), B2642, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B2669]
theorem treeEq2641 : B2641.tree = HexagonCover.NBand.M6900_7100.SplitData.node2641 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2642
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2669

theorem accepted2641 : B2641.accepted = true := by decide +kernel
theorem checked2641 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2641 (maskNeeds ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2641]
  exact B2641.sound accepted2641
#print axioms checked2641

def B2698 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293113491521476178833286651912, 98320, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1081).pointIds 1081), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1082).pointIds 1082)]
theorem treeEq2698 : B2698.tree = HexagonCover.NBand.M6900_7100.SplitData.node2698 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2697 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2698, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq2697 : B2697.tree = HexagonCover.NBand.M6900_7100.SplitData.node2697 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2698
  · rfl
  · rfl
  · rfl

def B2696 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B2697]
theorem treeEq2696 : B2696.tree = HexagonCover.NBand.M6900_7100.SplitData.node2696 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2697

def B2706 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 1461501659108975050497766536840632538439393738816] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1087).pointIds 1087)]
theorem treeEq2706 : B2706.tree = HexagonCover.NBand.M6900_7100.SplitData.node2706 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2705 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2706, (.leaf 5 (Common.fact 791).pointIds 791), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2705 : B2705.tree = HexagonCover.NBand.M6900_7100.SplitData.node2705 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2706
  · rfl
  · rfl

def B2704 : Block := .branch 132 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), B2705]
theorem treeEq2704 : B2704.tree = HexagonCover.NBand.M6900_7100.SplitData.node2704 := by
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
  · exact treeEq2705

def B2703 : Block := .branch 86 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920826709157852111578770551805025777794678848] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B2704, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), (.leaf 6 (Common.fact 1086).pointIds 1086)]
theorem treeEq2703 : B2703.tree = HexagonCover.NBand.M6900_7100.SplitData.node2703 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2704
  · rfl
  · rfl
  · rfl

def B2702 : Block := .branch 133 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), B2703]
theorem treeEq2702 : B2702.tree = HexagonCover.NBand.M6900_7100.SplitData.node2702 := by
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
  · exact treeEq2703

def B2701 : Block := .branch 157 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2702, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2701 : B2701.tree = HexagonCover.NBand.M6900_7100.SplitData.node2701 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2702
  · rfl
  · rfl

def B2700 : Block := .branch 171 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 375605920815820122110641547939723817587961211912256] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2701, (.leaf 6 (Common.fact 1085).pointIds 1085)]
theorem treeEq2700 : B2700.tree = HexagonCover.NBand.M6900_7100.SplitData.node2700 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2701
  · rfl

def B2699 : Block := .branch 160 ![10384593717070245552871351364092289, 906694580884853506442754, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 664).pointIds 664), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2700]
theorem treeEq2699 : B2699.tree = HexagonCover.NBand.M6900_7100.SplitData.node2699 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2700

def B2695 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2696, B2699, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq2695 : B2695.tree = HexagonCover.NBand.M6900_7100.SplitData.node2695 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2696
  · exact treeEq2699
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2709 : Block := .branch 132 ![385, 1538, 6148, 24584, 184114952359068824656518890058984872593374412816, 393248, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 977).pointIds 977)]
theorem treeEq2709 : B2709.tree = HexagonCover.NBand.M6900_7100.SplitData.node2709 := by
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

def B2708 : Block := .branch 157 ![385, 1538, 6148, 24584, 1427247692705959881058285969449495136382844944, 2993155353253731711777011654710880546081278819434528, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2709, (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 0 [] 0)]
theorem treeEq2708 : B2708.tree = HexagonCover.NBand.M6900_7100.SplitData.node2708 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2709
  · rfl
  · rfl

def B2707 : Block := .branch 171 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 953).pointIds 953), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2708, (.leaf 6 (Common.fact 976).pointIds 976)]
theorem treeEq2707 : B2707.tree = HexagonCover.NBand.M6900_7100.SplitData.node2707 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2708
  · rfl

def B2694 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B2695, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2707]
theorem treeEq2694 : B2694.tree = HexagonCover.NBand.M6900_7100.SplitData.node2694 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2695
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2707

def B2693 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2694, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq2693 : B2693.tree = HexagonCover.NBand.M6900_7100.SplitData.node2693 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2694
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2692 : Block := .branch 169 ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B2693, (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq2692 : B2692.tree = HexagonCover.NBand.M6900_7100.SplitData.node2692 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2693
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2691 : Block := .branch 109 ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B2692]
theorem treeEq2691 : B2691.tree = HexagonCover.NBand.M6900_7100.SplitData.node2691 := by
  change Tree.branch (109 : Fin 173) _ = Tree.branch (109 : Fin 173) _
  apply congrArg (Tree.branch (109 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2692

def B2690 : Block := .branch 150 ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B2691, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq2690 : B2690.tree = HexagonCover.NBand.M6900_7100.SplitData.node2690 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2691
  · rfl
  · rfl

theorem accepted2690 : B2690.accepted = true := by decide +kernel
theorem checked2690 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2690 (maskNeeds ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq2690]
  exact B2690.sound accepted2690
#print axioms checked2690

def Tip2639_2641 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2641 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2641
def B2680 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 931).pointIds 931)]
theorem treeEq2680 : B2680.tree = HexagonCover.NBand.M6900_7100.SplitData.node2680 := by
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

def B2679 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687003209070846658580470825024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2680, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 929).pointIds 929)]
theorem treeEq2679 : B2679.tree = HexagonCover.NBand.M6900_7100.SplitData.node2679 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2680
  · rfl
  · rfl

def B2678 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400368858333940594743008821312] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2679]
theorem treeEq2678 : B2678.tree = HexagonCover.NBand.M6900_7100.SplitData.node2678 := by
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
  · exact treeEq2679

def B2677 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400678343343761939811733602368] ![B2678, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq2677 : B2677.tree = HexagonCover.NBand.M6900_7100.SplitData.node2677 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2678
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2676 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2677, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2676 : B2676.tree = HexagonCover.NBand.M6900_7100.SplitData.node2676 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2677
  · rfl

def B2675 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2676, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq2675 : B2675.tree = HexagonCover.NBand.M6900_7100.SplitData.node2675 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2676
  · rfl
  · rfl

def B2640 : Block := .branch 86 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip2639_2641, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B2675]
theorem treeEq2640 : B2640.tree = HexagonCover.NBand.M6900_7100.SplitData.node2640 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2675

def B2686 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq2686 : B2686.tree = HexagonCover.NBand.M6900_7100.SplitData.node2686 := by
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

def B2685 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080882554756898504945696832] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2686, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq2685 : B2685.tree = HexagonCover.NBand.M6900_7100.SplitData.node2685 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2686
  · rfl
  · rfl

def B2684 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2685]
theorem treeEq2684 : B2684.tree = HexagonCover.NBand.M6900_7100.SplitData.node2684 := by
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
  · exact treeEq2685

def B2683 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446531817850834667483693120] ![B2684, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1076).pointIds 1076)]
theorem treeEq2683 : B2683.tree = HexagonCover.NBand.M6900_7100.SplitData.node2683 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2684
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2682 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2683, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2682 : B2682.tree = HexagonCover.NBand.M6900_7100.SplitData.node2682 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2683
  · rfl

def B2681 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2682, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq2681 : B2681.tree = HexagonCover.NBand.M6900_7100.SplitData.node2681 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2682
  · rfl
  · rfl

def B2639 : Block := .branch 78 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), B2640, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B2681]
theorem treeEq2639 : B2639.tree = HexagonCover.NBand.M6900_7100.SplitData.node2639 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2640
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2681

theorem accepted2639 : B2639.accepted = true := by decide +kernel
theorem checked2639 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2639 (maskNeeds ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2639]
  exact B2639.sound accepted2639
#print axioms checked2639

def Tip2637_2690 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2690 ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] checked2690
def Tip2637_2639 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2639 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2639
def B2689 : Block := .branch 125 ![10384593717070245552871351364092289, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), Tip2637_2690, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq2689 : B2689.tree = HexagonCover.NBand.M6900_7100.SplitData.node2689 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2716 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq2716 : B2716.tree = HexagonCover.NBand.M6900_7100.SplitData.node2716 := by
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

def B2715 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2716, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq2715 : B2715.tree = HexagonCover.NBand.M6900_7100.SplitData.node2715 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2716
  · rfl
  · rfl

def B2714 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2715]
theorem treeEq2714 : B2714.tree = HexagonCover.NBand.M6900_7100.SplitData.node2714 := by
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
  · exact treeEq2715

def B2713 : Block := .branch 171 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 1461501659108974401460659219987178972127352586304] ![B2714, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1090).pointIds 1090)]
theorem treeEq2713 : B2713.tree = HexagonCover.NBand.M6900_7100.SplitData.node2713 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2714
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2712 : Block := .branch 151 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2713, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2712 : B2712.tree = HexagonCover.NBand.M6900_7100.SplitData.node2712 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2713
  · rfl

def B2711 : Block := .branch 170 ![2475880078570760549798248833, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 375605920815820121461604440622870364021649170759744] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2712, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1089).pointIds 1089)]
theorem treeEq2711 : B2711.tree = HexagonCover.NBand.M6900_7100.SplitData.node2711 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2712
  · rfl
  · rfl

def B2710 : Block := .branch 160 ![2475880078570760549798248833, 738662397582310901250, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 688).pointIds 688), (.leaf 2 (Common.fact 1138).pointIds 1138), (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), B2711]
theorem treeEq2710 : B2710.tree = HexagonCover.NBand.M6900_7100.SplitData.node2710 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2711

def B2688 : Block := .branch 69 ![10384596192949733827821542456689025, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B2689, B2710, (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq2688 : B2688.tree = HexagonCover.NBand.M6900_7100.SplitData.node2688 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2689
  · exact treeEq2710
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2687 : Block := .branch 91 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![B2688, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq2687 : B2687.tree = HexagonCover.NBand.M6900_7100.SplitData.node2687 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2688
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2638 : Block := .branch 76 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 413).pointIds 413), (.leaf 1 (Common.fact 414).pointIds 414), Tip2637_2639, (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), B2687]
theorem treeEq2638 : B2638.tree = HexagonCover.NBand.M6900_7100.SplitData.node2638 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2687

def B2722 : Block := .branch 161 ![385, 1538, 18446884811197913092, 18889465931478580879368, 98320, 393248, 7108743963999289865625663087993656582482638809858112] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 722).pointIds 722), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1139).pointIds 1139)]
theorem treeEq2722 : B2722.tree = HexagonCover.NBand.M6900_7100.SplitData.node2722 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2721 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505376453642919676418801347854400] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2722]
theorem treeEq2721 : B2721.tree = HexagonCover.NBand.M6900_7100.SplitData.node2721 := by
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
  · exact treeEq2722

def B2720 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 6360455125685867571505376763127929497763870072635456] ![B2721, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2720 : B2720.tree = HexagonCover.NBand.M6900_7100.SplitData.node2720 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2721
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2719 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38704515693599612171477000, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2720, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2719 : B2719.tree = HexagonCover.NBand.M6900_7100.SplitData.node2719 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2720
  · rfl

def B2718 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2719, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2718 : B2718.tree = HexagonCover.NBand.M6900_7100.SplitData.node2718 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2719
  · rfl
  · rfl

def B2717 : Block := .branch 172 ![385, 792634633928836610, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1092).pointIds 1092), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2718]
theorem treeEq2717 : B2717.tree = HexagonCover.NBand.M6900_7100.SplitData.node2717 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2718

def B2637 : Block := .branch 74 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 455).pointIds 455), (.leaf 1 (Common.fact 456).pointIds 456), B2638, B2717, (.leaf 4 (Common.fact 457).pointIds 457), (.leaf 5 (Common.fact 458).pointIds 458), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq2637 : B2637.tree = HexagonCover.NBand.M6900_7100.SplitData.node2637 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2638
  · exact treeEq2717
  · rfl
  · rfl
  · rfl

theorem accepted2637 : B2637.accepted = true := by decide +kernel
theorem checked2637 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2637 (maskNeeds ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2637]
  exact B2637.sound accepted2637
#print axioms checked2637

end HexagonCover.NBand.M6900_7100.SplitTree.Run0036
