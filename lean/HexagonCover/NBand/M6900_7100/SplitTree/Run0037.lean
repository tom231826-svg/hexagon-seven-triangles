import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0036
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0037
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2635_2637 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2637 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0036.checked2637
def B2728 : Block := .branch 161 ![385, 1538, 18446884811197913092, 38695070960633872881049608, 98320, 393248, 7108743963999289865625663087993656582482638809858112] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 755).pointIds 755), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1139).pointIds 1139)]
theorem treeEq2728 : B2728.tree = HexagonCover.NBand.M6900_7100.SplitData.node2728 := by
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

def B2727 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505376453642919676418801347854400] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2728]
theorem treeEq2727 : B2727.tree = HexagonCover.NBand.M6900_7100.SplitData.node2727 := by
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
  · exact treeEq2728

def B2726 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 6360455125685867571505376763127929497763870072635456] ![B2727, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2726 : B2726.tree = HexagonCover.NBand.M6900_7100.SplitData.node2726 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2727
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2725 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38695070960633872881049608, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2726, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2725 : B2725.tree = HexagonCover.NBand.M6900_7100.SplitData.node2725 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2726
  · rfl

def B2724 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2725, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2724 : B2724.tree = HexagonCover.NBand.M6900_7100.SplitData.node2724 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2725
  · rfl
  · rfl

def B2723 : Block := .branch 172 ![385, 792634633928836610, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1100).pointIds 1100), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2724]
theorem treeEq2723 : B2723.tree = HexagonCover.NBand.M6900_7100.SplitData.node2723 := by
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
  · exact treeEq2724

def B2636 : Block := .branch 73 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 451).pointIds 451), Tip2635_2637, B2723, (.leaf 4 (Common.fact 452).pointIds 452), (.leaf 5 (Common.fact 453).pointIds 453), (.leaf 6 (Common.fact 454).pointIds 454)]
theorem treeEq2636 : B2636.tree = HexagonCover.NBand.M6900_7100.SplitData.node2636 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2723
  · rfl
  · rfl
  · rfl

def B2734 : Block := .branch 161 ![385, 1538, 18446884811197913092, 38690348594151003235835912, 98320, 393248, 7108743963999289865625663087993656582482638809858112] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1139).pointIds 1139)]
theorem treeEq2734 : B2734.tree = HexagonCover.NBand.M6900_7100.SplitData.node2734 := by
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

def B2733 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505376453642919676418801347854400] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2734]
theorem treeEq2733 : B2733.tree = HexagonCover.NBand.M6900_7100.SplitData.node2733 := by
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
  · exact treeEq2734

def B2732 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 6360455125685867571505376763127929497763870072635456] ![B2733, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1094).pointIds 1094)]
theorem treeEq2732 : B2732.tree = HexagonCover.NBand.M6900_7100.SplitData.node2732 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2733
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2731 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38690348594151003235835912, 1496578390250690941220513797844458536875243115479056, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2732, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2731 : B2731.tree = HexagonCover.NBand.M6900_7100.SplitData.node2731 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2732
  · rfl

def B2730 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 6360455125685867571505693830520491465786778610827328] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2731, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1093).pointIds 1093)]
theorem treeEq2730 : B2730.tree = HexagonCover.NBand.M6900_7100.SplitData.node2730 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2731
  · rfl
  · rfl

def B2729 : Block := .branch 172 ![385, 792634633928836610, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), (.leaf 3 (Common.fact 1101).pointIds 1101), (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), B2730]
theorem treeEq2729 : B2729.tree = HexagonCover.NBand.M6900_7100.SplitData.node2729 := by
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
  · exact treeEq2730

def B2635 : Block := .branch 72 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B2636, B2729, (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 425).pointIds 425)]
theorem treeEq2635 : B2635.tree = HexagonCover.NBand.M6900_7100.SplitData.node2635 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2636
  · exact treeEq2729
  · rfl
  · rfl
  · rfl

theorem accepted2635 : B2635.accepted = true := by decide +kernel
theorem checked2635 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2635 (maskNeeds ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2635]
  exact B2635.sound accepted2635
#print axioms checked2635

def Tip2632_2635 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2635 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2635
def B2740 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 98320, 393248, 751211841609862171439950978327882504329706423713856] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 1140).pointIds 1140)]
theorem treeEq2740 : B2740.tree = HexagonCover.NBand.M6900_7100.SplitData.node2740 := by
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
  · rfl

def B2739 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2740]
theorem treeEq2739 : B2739.tree = HexagonCover.NBand.M6900_7100.SplitData.node2739 := by
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
  · exact treeEq2740

def B2738 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 377067422453151024379807970637523872642856417493056] ![B2739, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1103).pointIds 1103)]
theorem treeEq2738 : B2738.tree = HexagonCover.NBand.M6900_7100.SplitData.node2738 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2739
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2737 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2738, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2737 : B2737.tree = HexagonCover.NBand.M6900_7100.SplitData.node2737 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2738
  · rfl

def B2736 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 377067422453151024379808125380028783315390779883584] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2737, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1102).pointIds 1102)]
theorem treeEq2736 : B2736.tree = HexagonCover.NBand.M6900_7100.SplitData.node2736 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2737
  · rfl
  · rfl

def B2735 : Block := .branch 161 ![385, 792634633928836610, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), B2736]
theorem treeEq2735 : B2735.tree = HexagonCover.NBand.M6900_7100.SplitData.node2735 := by
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
  · exact treeEq2736

def B2634 : Block := .branch 71 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), Tip2632_2635, B2735, (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 0 [] 0)]
theorem treeEq2634 : B2634.tree = HexagonCover.NBand.M6900_7100.SplitData.node2634 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2735
  · rfl
  · rfl
  · rfl

def B2746 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 1496577676637733623982043299532301799565491506872336, 393248, 1122433257491911512663687080580618449900027004846144] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), (.leaf 4 (Common.fact 1116).pointIds 1116), (.leaf 5 (Common.fact 322).pointIds 322), (.leaf 6 (Common.fact 1142).pointIds 1142)]
theorem treeEq2746 : B2746.tree = HexagonCover.NBand.M6900_7100.SplitData.node2746 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2745 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 1122433257491911512663687080580618449900027004846144] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), B2746, (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 1141).pointIds 1141)]
theorem treeEq2745 : B2745.tree = HexagonCover.NBand.M6900_7100.SplitData.node2745 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2746
  · rfl
  · rfl

def B2744 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400446229881543836189542842432] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2745]
theorem treeEq2744 : B2744.tree = HexagonCover.NBand.M6900_7100.SplitData.node2744 := by
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
  · exact treeEq2745

def B2743 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229881543836189542842432] ![B2744, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1107).pointIds 1107)]
theorem treeEq2743 : B2743.tree = HexagonCover.NBand.M6900_7100.SplitData.node2743 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2744
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2742 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2743, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2742 : B2742.tree = HexagonCover.NBand.M6900_7100.SplitData.node2742 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2743
  · rfl

def B2741 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714891365181258267623488] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2742, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1106).pointIds 1106)]
theorem treeEq2741 : B2741.tree = HexagonCover.NBand.M6900_7100.SplitData.node2741 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2742
  · rfl
  · rfl

def B2633 : Block := .branch 68 ![10384593717069655257060992658440577, 148366587223605249538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 445).pointIds 445), B2634, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 447).pointIds 447), (.leaf 4 (Common.fact 448).pointIds 448), (.leaf 5 (Common.fact 449).pointIds 449), B2741]
theorem treeEq2633 : B2633.tree = HexagonCover.NBand.M6900_7100.SplitData.node2633 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2634
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2741

def B2751 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080580470875947437328433216] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), (.leaf 6 (Common.fact 1120).pointIds 1120)]
theorem treeEq2751 : B2751.tree = HexagonCover.NBand.M6900_7100.SplitData.node2751 := by
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
  · rfl

def B2750 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 648519445852980738, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446229733969883599866429504] ![(.leaf 0 (Common.fact 928).pointIds 928), (.leaf 1 (Common.fact 1130).pointIds 1130), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2751]
theorem treeEq2750 : B2750.tree = HexagonCover.NBand.M6900_7100.SplitData.node2750 := by
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
  · exact treeEq2751

def B2749 : Block := .branch 171 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218543400446229733969883599866429504] ![B2750, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1119).pointIds 1119)]
theorem treeEq2749 : B2749.tree = HexagonCover.NBand.M6900_7100.SplitData.node2749 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2750
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2748 : Block := .branch 151 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2749, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2748 : B2748.tree = HexagonCover.NBand.M6900_7100.SplitData.node2748 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2749
  · rfl

def B2747 : Block := .branch 170 ![385, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714743791228668591210560] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2748, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 1118).pointIds 1118)]
theorem treeEq2747 : B2747.tree = HexagonCover.NBand.M6900_7100.SplitData.node2747 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2748
  · rfl
  · rfl

def B2632 : Block := .branch 67 ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 439).pointIds 439), B2633, (.leaf 2 (Common.fact 440).pointIds 440), (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), B2747]
theorem treeEq2632 : B2632.tree = HexagonCover.NBand.M6900_7100.SplitData.node2632 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2633
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2747

theorem accepted2632 : B2632.accepted = true := by decide +kernel
theorem checked2632 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2632 (maskNeeds ![10384593717069655257060992658440577, 792634633928836610, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2632]
  exact B2632.sound accepted2632
#print axioms checked2632

def B2774 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq2774 : B2774.tree = HexagonCover.NBand.M6900_7100.SplitData.node2774 := by
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

def B2773 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144424753675518176056541098525785438169291292736] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2774, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1046).pointIds 1046)]
theorem treeEq2773 : B2773.tree = HexagonCover.NBand.M6900_7100.SplitData.node2773 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2774
  · rfl
  · rfl
  · rfl

def B2772 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 468).pointIds 468), (.leaf 5 (Common.fact 156).pointIds 156), B2773]
theorem treeEq2772 : B2772.tree = HexagonCover.NBand.M6900_7100.SplitData.node2772 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2773

def B2771 : Block := .branch 166 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 2854495385411919762116571938898990272765886496, 374144419178489218543400755714596217276078914797632] ![B2772, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2771 : B2771.tree = HexagonCover.NBand.M6900_7100.SplitData.node2771 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2772
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2770 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846353304459082801411451530724212047888, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 465).pointIds 465), B2771, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2770 : B2770.tree = HexagonCover.NBand.M6900_7100.SplitData.node2770 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2771
  · rfl

def B2783 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1058).pointIds 1058)]
theorem treeEq2783 : B2783.tree = HexagonCover.NBand.M6900_7100.SplitData.node2783 := by
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

def B2782 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 1870722095805333807108175665424439698836535683579968] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2783, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1057).pointIds 1057)]
theorem treeEq2782 : B2782.tree = HexagonCover.NBand.M6900_7100.SplitData.node2782 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2783
  · rfl
  · rfl
  · rfl

def B2781 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 186255823898127764478106319013159115297948532752, 393248, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 841).pointIds 841), (.leaf 5 (Common.fact 660).pointIds 660), B2782]
theorem treeEq2781 : B2781.tree = HexagonCover.NBand.M6900_7100.SplitData.node2781 := by
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
  · exact treeEq2782

def B2780 : Block := .branch 151 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), B2781, (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2780 : B2780.tree = HexagonCover.NBand.M6900_7100.SplitData.node2780 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2781
  · rfl
  · rfl

def B2779 : Block := .branch 132 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 996).pointIds 996), (.leaf 5 (Common.fact 221).pointIds 221), B2780]
theorem treeEq2779 : B2779.tree = HexagonCover.NBand.M6900_7100.SplitData.node2779 := by
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
  · exact treeEq2780

def B2778 : Block := .branch 133 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 183401328512715844715989747074260125025183039504, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 210).pointIds 210), (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 995).pointIds 995), (.leaf 5 (Common.fact 215).pointIds 215), B2779]
theorem treeEq2778 : B2778.tree = HexagonCover.NBand.M6900_7100.SplitData.node2778 := by
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
  · exact treeEq2779

def B2777 : Block := .branch 157 ![385, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 2993155353253689176481146537402947624255349848408096, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 205).pointIds 205), (.leaf 1 (Common.fact 206).pointIds 206), (.leaf 2 (Common.fact 207).pointIds 207), (.leaf 3 (Common.fact 208).pointIds 208), B2778, (.leaf 5 (Common.fact 994).pointIds 994), (.leaf 0 [] 0)]
theorem treeEq2777 : B2777.tree = HexagonCover.NBand.M6900_7100.SplitData.node2777 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2778
  · rfl
  · rfl

def B2776 : Block := .branch 171 ![748288838313422304507415652620848621927823526855041, 144116287587485186, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 830).pointIds 830), (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), B2777, (.leaf 6 (Common.fact 1054).pointIds 1054)]
theorem treeEq2776 : B2776.tree = HexagonCover.NBand.M6900_7100.SplitData.node2776 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2777
  · rfl

def B2775 : Block := .branch 169 ![10387129018270111715863986064851329, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218867919309373022944059234935373888] ![B2776, (.leaf 1 (Common.fact 1049).pointIds 1049), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 489).pointIds 489)]
theorem treeEq2775 : B2775.tree = HexagonCover.NBand.M6900_7100.SplitData.node2775 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2776
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2769 : Block := .branch 108 ![10387129018270111715863986064851329, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 318).pointIds 318), (.leaf 1 (Common.fact 319).pointIds 319), (.leaf 2 (Common.fact 320).pointIds 320), (.leaf 3 (Common.fact 321).pointIds 321), B2770, (.leaf 5 (Common.fact 322).pointIds 322), B2775]
theorem treeEq2769 : B2769.tree = HexagonCover.NBand.M6900_7100.SplitData.node2769 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2770
  · rfl
  · exact treeEq2775

theorem accepted2769 : B2769.accepted = true := by decide +kernel
theorem checked2769 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2769 (maskNeeds ![10387129018270111715863986064851329, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2769]
  exact B2769.sound accepted2769
#print axioms checked2769

def Tip2767_2769 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node2769 ![10387129018270111715863986064851329, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] checked2769
def B2791 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 605).pointIds 605)]
theorem treeEq2791 : B2791.tree = HexagonCover.NBand.M6900_7100.SplitData.node2791 := by
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

def B2790 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 374144419178489218545935747430042854734003596427328] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B2791, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 603).pointIds 603)]
theorem treeEq2790 : B2790.tree = HexagonCover.NBand.M6900_7100.SplitData.node2790 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2791
  · rfl
  · rfl

def B2789 : Block := .branch 166 ![385, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2790, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq2789 : B2789.tree = HexagonCover.NBand.M6900_7100.SplitData.node2789 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2790
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2788 : Block := .branch 164 ![2993155353253689176481149013283026195015899646263681, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1060).pointIds 1060), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2789]
theorem treeEq2788 : B2788.tree = HexagonCover.NBand.M6900_7100.SplitData.node2788 := by
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
  · exact treeEq2789

def B2787 : Block := .branch 169 ![2993155353253689176481149013283026195015899646263681, 618970019642691236961191426, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 1001).pointIds 1001), (.leaf 1 (Common.fact 1049).pointIds 1049), (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B2788]
theorem treeEq2787 : B2787.tree = HexagonCover.NBand.M6900_7100.SplitData.node2787 := by
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
  · exact treeEq2788

def B2786 : Block := .branch 171 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 374144419178489218545936056915052676079072321208384] ![B2787, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1059).pointIds 1059)]
theorem treeEq2786 : B2786.tree = HexagonCover.NBand.M6900_7100.SplitData.node2786 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2787
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2785 : Block := .branch 151 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2786, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2785 : B2785.tree = HexagonCover.NBand.M6900_7100.SplitData.node2785 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2786
  · rfl

def B2784 : Block := .branch 170 ![2475880078570760549798248833, 618970019786806425037047298, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218545936056915052676079072321208384] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2785, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 729).pointIds 729)]
theorem treeEq2784 : B2784.tree = HexagonCover.NBand.M6900_7100.SplitData.node2784 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2785
  · rfl
  · rfl

def B2768 : Block := .branch 101 ![10384596192949733827821542456689025, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![Tip2767_2769, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), B2784]
theorem treeEq2768 : B2768.tree = HexagonCover.NBand.M6900_7100.SplitData.node2768 := by
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
  · exact treeEq2784

def B2793 : Block := .branch 161 ![385, 1538, 18446884811197913092, 5986310706507378352962293152177147703846966877249544, 98320, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), (.leaf 2 (Common.fact 1129).pointIds 1129), (.leaf 3 (Common.fact 1048).pointIds 1048), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 1062).pointIds 1062)]
theorem treeEq2793 : B2793.tree = HexagonCover.NBand.M6900_7100.SplitData.node2793 := by
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

def B2792 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 77371252455336267181219848, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543402922109664966691559988265024] ![(.leaf 0 (Common.fact 1009).pointIds 1009), (.leaf 1 (Common.fact 1127).pointIds 1127), (.leaf 2 (Common.fact 1128).pointIds 1128), B2793, (.leaf 4 (Common.fact 946).pointIds 946), (.leaf 5 (Common.fact 947).pointIds 947), (.leaf 6 (Common.fact 1061).pointIds 1061)]
theorem treeEq2792 : B2792.tree = HexagonCover.NBand.M6900_7100.SplitData.node2792 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2793
  · rfl
  · rfl
  · rfl

def B2767 : Block := .branch 91 ![10384593717069655257060992658440577, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![B2768, (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), (.leaf 3 (Common.fact 333).pointIds 333), (.leaf 4 (Common.fact 334).pointIds 334), (.leaf 5 (Common.fact 335).pointIds 335), B2792]
theorem treeEq2767 : B2767.tree = HexagonCover.NBand.M6900_7100.SplitData.node2767 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2792

theorem accepted2767 : B2767.accepted = true := by decide +kernel
theorem checked2767 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2767 (maskNeeds ![10384593717069655257060992658440577, 618970019786806425037047298, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq2767]
  exact B2767.sound accepted2767
#print axioms checked2767

def B2813 : Block := .branch 89 ![385, 748288838313422294120286634652968360968594267309570, 6148, 24584, 98320, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 1143).pointIds 1143), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), (.leaf 6 (Common.fact 1144).pointIds 1144)]
theorem treeEq2813 : B2813.tree = HexagonCover.NBand.M6900_7100.SplitData.node2813 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2812 : Block := .branch 169 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 928).pointIds 928), B2813, (.leaf 2 (Common.fact 1131).pointIds 1131), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq2812 : B2812.tree = HexagonCover.NBand.M6900_7100.SplitData.node2812 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2813
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2811 : Block := .branch 163 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B2812]
theorem treeEq2811 : B2811.tree = HexagonCover.NBand.M6900_7100.SplitData.node2811 := by
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
  · exact treeEq2812

def B2810 : Block := .branch 165 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B2811, (.leaf 0 [] 0)]
theorem treeEq2810 : B2810.tree = HexagonCover.NBand.M6900_7100.SplitData.node2810 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2811
  · rfl

def B2809 : Block := .branch 167 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 393248, 374144419178489218543083765693286704589437557801024] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B2810, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq2809 : B2809.tree = HexagonCover.NBand.M6900_7100.SplitData.node2809 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2810
  · rfl

def B2808 : Block := .branch 142 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B2809, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq2808 : B2808.tree = HexagonCover.NBand.M6900_7100.SplitData.node2808 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2809
  · rfl
  · rfl

def B2807 : Block := .branch 124 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 397528445375783665234659635666804290254306654289984] ![B2808, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 1072).pointIds 1072)]
theorem treeEq2807 : B2807.tree = HexagonCover.NBand.M6900_7100.SplitData.node2807 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2808
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2806 : Block := .branch 164 ![2993155353253689176481146537402947624255349848015233, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400678343343761939811733602368] ![(.leaf 0 (Common.fact 1064).pointIds 1064), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), (.leaf 4 (Common.fact 179).pointIds 179), (.leaf 5 (Common.fact 180).pointIds 180), B2807]
theorem treeEq2806 : B2806.tree = HexagonCover.NBand.M6900_7100.SplitData.node2806 := by
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
  · exact treeEq2807

def B2805 : Block := .branch 171 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400678343343761939811733602368] ![B2806, (.leaf 1 (Common.fact 1132).pointIds 1132), (.leaf 2 (Common.fact 1133).pointIds 1133), (.leaf 3 (Common.fact 1053).pointIds 1053), (.leaf 4 (Common.fact 956).pointIds 956), (.leaf 5 (Common.fact 991).pointIds 991), (.leaf 6 (Common.fact 1071).pointIds 1071)]
theorem treeEq2805 : B2805.tree = HexagonCover.NBand.M6900_7100.SplitData.node2805 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2806
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2804 : Block := .branch 151 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B2805, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq2804 : B2804.tree = HexagonCover.NBand.M6900_7100.SplitData.node2804 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2805
  · rfl

def B2803 : Block := .branch 170 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 837).pointIds 837), (.leaf 1 (Common.fact 1134).pointIds 1134), (.leaf 2 (Common.fact 1135).pointIds 1135), (.leaf 3 (Common.fact 658).pointIds 658), B2804, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq2803 : B2803.tree = HexagonCover.NBand.M6900_7100.SplitData.node2803 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2804
  · rfl
  · rfl

theorem accepted2803 : B2803.accepted = true := by decide +kernel
theorem checked2803 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node2803 (maskNeeds ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896]) := by
  rw [← treeEq2803]
  exact B2803.sound accepted2803
#print axioms checked2803

end HexagonCover.NBand.M6900_7100.SplitTree.Run0037
