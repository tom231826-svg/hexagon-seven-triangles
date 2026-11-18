import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0038
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0039
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2692_2694 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2694 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0038.checked2694
def B2775 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 649037107316853453566312041250832, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 820).pointIds 820), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq2775 : B2775.tree = HexagonCover.NBand.M7300_7500.SplitData.node2775 := by
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

def B2774 : Block := .branch 109 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), B2775, (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 819).pointIds 819)]
theorem treeEq2774 : B2774.tree = HexagonCover.NBand.M7300_7500.SplitData.node2774 := by
  change Tree.branch (109 : Fin 172) _ = Tree.branch (109 : Fin 172) _
  apply congrArg (Tree.branch (109 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2775
  · rfl
  · rfl

def B2773 : Block := .branch 124 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 24845527856403421092719772419320573847871486951488] ![B2774, (.leaf 1 (Common.fact 211).pointIds 211), (.leaf 2 (Common.fact 212).pointIds 212), (.leaf 3 (Common.fact 213).pointIds 213), (.leaf 4 (Common.fact 214).pointIds 214), (.leaf 5 (Common.fact 215).pointIds 215), (.leaf 6 (Common.fact 818).pointIds 818)]
theorem treeEq2773 : B2773.tree = HexagonCover.NBand.M7300_7500.SplitData.node2773 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2774
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2772 : Block := .branch 160 ![385, 302821750715115510957570, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 863).pointIds 863), (.leaf 2 (Common.fact 859).pointIds 859), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B2773]
theorem treeEq2772 : B2772.tree = HexagonCover.NBand.M7300_7500.SplitData.node2772 := by
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
  · exact treeEq2773

def B2771 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 23384026219072518174516087586604290828215554408512] ![(.leaf 0 (Common.fact 753).pointIds 753), B2772, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq2771 : B2771.tree = HexagonCover.NBand.M7300_7500.SplitData.node2771 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2772
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2770 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2771]
theorem treeEq2770 : B2770.tree = HexagonCover.NBand.M7300_7500.SplitData.node2770 := by
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
  · exact treeEq2771

def B2769 : Block := .branch 169 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B2770, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2769 : B2769.tree = HexagonCover.NBand.M7300_7500.SplitData.node2769 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2770
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2768 : Block := .branch 170 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2769, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2768 : B2768.tree = HexagonCover.NBand.M7300_7500.SplitData.node2768 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2769
  · rfl

def B2767 : Block := .branch 171 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2768, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq2767 : B2767.tree = HexagonCover.NBand.M7300_7500.SplitData.node2767 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2768
  · rfl
  · rfl

def B2693 : Block := .branch 80 ![385, 302231599019944881161730, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip2692_2694, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B2767]
theorem treeEq2693 : B2693.tree = HexagonCover.NBand.M7300_7500.SplitData.node2693 := by
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
  · exact treeEq2767

def B2783 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 890).pointIds 890), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq2783 : B2783.tree = HexagonCover.NBand.M7300_7500.SplitData.node2783 := by
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

def B2782 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2783, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq2782 : B2782.tree = HexagonCover.NBand.M7300_7500.SplitData.node2782 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2783
  · rfl
  · rfl

def B2781 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B2782, (.leaf 6 (Common.fact 889).pointIds 889)]
theorem treeEq2781 : B2781.tree = HexagonCover.NBand.M7300_7500.SplitData.node2781 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2782
  · rfl

def B2780 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B2781, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2780 : B2780.tree = HexagonCover.NBand.M7300_7500.SplitData.node2780 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2781
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2779 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2780]
theorem treeEq2779 : B2779.tree = HexagonCover.NBand.M7300_7500.SplitData.node2779 := by
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
  · exact treeEq2780

def B2778 : Block := .branch 169 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B2779, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2778 : B2778.tree = HexagonCover.NBand.M7300_7500.SplitData.node2778 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2779
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2777 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2778, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2777 : B2777.tree = HexagonCover.NBand.M7300_7500.SplitData.node2777 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2778
  · rfl

def B2776 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2777, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq2776 : B2776.tree = HexagonCover.NBand.M7300_7500.SplitData.node2776 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2777
  · rfl
  · rfl

def B2692 : Block := .branch 78 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B2693, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B2776]
theorem treeEq2692 : B2692.tree = HexagonCover.NBand.M7300_7500.SplitData.node2692 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2693
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2776

theorem accepted2692 : B2692.accepted = true := by decide +kernel
theorem checked2692 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2692 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2692]
  exact B2692.sound accepted2692
#print axioms checked2692

def B2832 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938599789055153162841936079095272624131276832, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2832 : B2832.tree = HexagonCover.NBand.M7300_7500.SplitData.node2832 := by
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

def B2831 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285381374410753538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![B2832, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2831 : B2831.tree = HexagonCover.NBand.M7300_7500.SplitData.node2831 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2832
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2830 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B2831, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2830 : B2830.tree = HexagonCover.NBand.M7300_7500.SplitData.node2830 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2831
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2829 : Block := .branch 169 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294286866390594440719509225536] ![B2830, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2829 : B2829.tree = HexagonCover.NBand.M7300_7500.SplitData.node2829 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2830
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2828 : Block := .branch 170 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156072452721829093742851929861917165008415981584, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 837).pointIds 837), B2829, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2828 : B2828.tree = HexagonCover.NBand.M7300_7500.SplitData.node2828 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2829
  · rfl

def B2827 : Block := .branch 171 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 20461022944410712338109026197255726519343239397440] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2828, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2827 : B2827.tree = HexagonCover.NBand.M7300_7500.SplitData.node2827 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2828
  · rfl
  · rfl

def B2826 : Block := .branch 162 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 745).pointIds 745), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), B2827]
theorem treeEq2826 : B2826.tree = HexagonCover.NBand.M7300_7500.SplitData.node2826 := by
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
  · exact treeEq2827

def B2825 : Block := .branch 78 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 134).pointIds 134), B2826, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2825 : B2825.tree = HexagonCover.NBand.M7300_7500.SplitData.node2825 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2826
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2824 : Block := .branch 68 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 901).pointIds 901), B2825, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq2824 : B2824.tree = HexagonCover.NBand.M7300_7500.SplitData.node2824 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2825
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2823 : Block := .branch 112 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2824, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq2823 : B2823.tree = HexagonCover.NBand.M7300_7500.SplitData.node2823 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2824
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2822 : Block := .branch 163 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2823]
theorem treeEq2822 : B2822.tree = HexagonCover.NBand.M7300_7500.SplitData.node2822 := by
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
  · exact treeEq2823

def B2821 : Block := .branch 165 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2822, (.leaf 0 [] 0)]
theorem treeEq2821 : B2821.tree = HexagonCover.NBand.M7300_7500.SplitData.node2821 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2822
  · rfl

def B2820 : Block := .branch 167 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2821, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2820 : B2820.tree = HexagonCover.NBand.M7300_7500.SplitData.node2820 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2821
  · rfl

def B2819 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2820, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2819 : B2819.tree = HexagonCover.NBand.M7300_7500.SplitData.node2819 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2820
  · rfl
  · rfl

def B2818 : Block := .branch 144 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2819, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2818 : B2818.tree = HexagonCover.NBand.M7300_7500.SplitData.node2818 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2819
  · rfl

def B2817 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 830).pointIds 830), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2818]
theorem treeEq2817 : B2817.tree = HexagonCover.NBand.M7300_7500.SplitData.node2817 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2818

theorem accepted2817 : B2817.accepted = true := by decide +kernel
theorem checked2817 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2817 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2817]
  exact B2817.sound accepted2817
#print axioms checked2817

def B2848 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938599789055153162841936079095272624131276832, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2848 : B2848.tree = HexagonCover.NBand.M7300_7500.SplitData.node2848 := by
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

def B2847 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285381374410753538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![B2848, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2847 : B2847.tree = HexagonCover.NBand.M7300_7500.SplitData.node2847 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2848
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2846 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B2847, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2846 : B2846.tree = HexagonCover.NBand.M7300_7500.SplitData.node2846 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2847
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2845 : Block := .branch 169 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294286866390594440719509225536] ![B2846, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2845 : B2845.tree = HexagonCover.NBand.M7300_7500.SplitData.node2845 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2846
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2844 : Block := .branch 170 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156072452721829093742851929861917165008415981584, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 837).pointIds 837), B2845, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2844 : B2844.tree = HexagonCover.NBand.M7300_7500.SplitData.node2844 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2845
  · rfl

def B2843 : Block := .branch 171 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 20461022944410712338109026197255726519343239397440] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2844, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2843 : B2843.tree = HexagonCover.NBand.M7300_7500.SplitData.node2843 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2844
  · rfl
  · rfl

def B2842 : Block := .branch 162 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 767).pointIds 767), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), B2843]
theorem treeEq2842 : B2842.tree = HexagonCover.NBand.M7300_7500.SplitData.node2842 := by
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
  · exact treeEq2843

def B2841 : Block := .branch 78 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 134).pointIds 134), B2842, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2841 : B2841.tree = HexagonCover.NBand.M7300_7500.SplitData.node2841 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2842
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2840 : Block := .branch 68 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 901).pointIds 901), B2841, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq2840 : B2840.tree = HexagonCover.NBand.M7300_7500.SplitData.node2840 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2841
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2839 : Block := .branch 112 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2840, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq2839 : B2839.tree = HexagonCover.NBand.M7300_7500.SplitData.node2839 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2840
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2838 : Block := .branch 163 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2839]
theorem treeEq2838 : B2838.tree = HexagonCover.NBand.M7300_7500.SplitData.node2838 := by
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
  · exact treeEq2839

def B2837 : Block := .branch 165 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2838, (.leaf 0 [] 0)]
theorem treeEq2837 : B2837.tree = HexagonCover.NBand.M7300_7500.SplitData.node2837 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2838
  · rfl

def B2836 : Block := .branch 167 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2837, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2836 : B2836.tree = HexagonCover.NBand.M7300_7500.SplitData.node2836 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2837
  · rfl

def B2835 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2836, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2835 : B2835.tree = HexagonCover.NBand.M7300_7500.SplitData.node2835 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2836
  · rfl
  · rfl

def B2834 : Block := .branch 144 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2835, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2834 : B2834.tree = HexagonCover.NBand.M7300_7500.SplitData.node2834 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2835
  · rfl

def B2833 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 840).pointIds 840), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2834]
theorem treeEq2833 : B2833.tree = HexagonCover.NBand.M7300_7500.SplitData.node2833 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2834

theorem accepted2833 : B2833.accepted = true := by decide +kernel
theorem checked2833 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2833 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2833]
  exact B2833.sound accepted2833
#print axioms checked2833

def B2864 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938599789055153162841936079095272624131276832, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2864 : B2864.tree = HexagonCover.NBand.M7300_7500.SplitData.node2864 := by
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

def B2863 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285381374410753538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![B2864, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2863 : B2863.tree = HexagonCover.NBand.M7300_7500.SplitData.node2863 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2864
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2862 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B2863, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2862 : B2862.tree = HexagonCover.NBand.M7300_7500.SplitData.node2862 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2863
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2861 : Block := .branch 169 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294286866390594440719509225536] ![B2862, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2861 : B2861.tree = HexagonCover.NBand.M7300_7500.SplitData.node2861 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2862
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2860 : Block := .branch 170 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156072452721829093742851929861917165008415981584, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 837).pointIds 837), B2861, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2860 : B2860.tree = HexagonCover.NBand.M7300_7500.SplitData.node2860 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2861
  · rfl

def B2859 : Block := .branch 171 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 20461022944410712338109026197255726519343239397440] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2860, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2859 : B2859.tree = HexagonCover.NBand.M7300_7500.SplitData.node2859 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2860
  · rfl
  · rfl

def B2858 : Block := .branch 162 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), B2859]
theorem treeEq2858 : B2858.tree = HexagonCover.NBand.M7300_7500.SplitData.node2858 := by
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
  · exact treeEq2859

def B2857 : Block := .branch 78 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 134).pointIds 134), B2858, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2857 : B2857.tree = HexagonCover.NBand.M7300_7500.SplitData.node2857 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2858
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2856 : Block := .branch 68 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 901).pointIds 901), B2857, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq2856 : B2856.tree = HexagonCover.NBand.M7300_7500.SplitData.node2856 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2857
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2855 : Block := .branch 112 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2856, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq2855 : B2855.tree = HexagonCover.NBand.M7300_7500.SplitData.node2855 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2856
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2854 : Block := .branch 163 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2855]
theorem treeEq2854 : B2854.tree = HexagonCover.NBand.M7300_7500.SplitData.node2854 := by
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
  · exact treeEq2855

def B2853 : Block := .branch 165 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2854, (.leaf 0 [] 0)]
theorem treeEq2853 : B2853.tree = HexagonCover.NBand.M7300_7500.SplitData.node2853 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2854
  · rfl

def B2852 : Block := .branch 167 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2853, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2852 : B2852.tree = HexagonCover.NBand.M7300_7500.SplitData.node2852 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2853
  · rfl

def B2851 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2852, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2851 : B2851.tree = HexagonCover.NBand.M7300_7500.SplitData.node2851 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2852
  · rfl
  · rfl

def B2850 : Block := .branch 144 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2851, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2850 : B2850.tree = HexagonCover.NBand.M7300_7500.SplitData.node2850 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2851
  · rfl

def B2849 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 841).pointIds 841), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2850]
theorem treeEq2849 : B2849.tree = HexagonCover.NBand.M7300_7500.SplitData.node2849 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2850

theorem accepted2849 : B2849.accepted = true := by decide +kernel
theorem checked2849 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2849 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq2849]
  exact B2849.sound accepted2849
#print axioms checked2849

end HexagonCover.NBand.M7300_7500.SplitTree.Run0039
