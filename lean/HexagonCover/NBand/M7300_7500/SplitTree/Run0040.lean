import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0037
import HexagonCover.NBand.M7300_7500.SplitTree.Run0038
import HexagonCover.NBand.M7300_7500.SplitTree.Run0039
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0040
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip2688_2787 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2787 ![10384596192949733827821542456689025, 442865974056616723970, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0038.checked2787
def Tip2688_2692 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2692 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0039.checked2692
def Tip2688_2817 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2817 ![385, 144116287587485186, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0039.checked2817
def Tip2688_2833 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2833 ![385, 144116287587485186, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0039.checked2833
def Tip2688_2849 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2849 ![385, 144116287587485186, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0039.checked2849
def B2816 : Block := .branch 121 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), (.leaf 4 (Common.fact 898).pointIds 898), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 899).pointIds 899)]
theorem treeEq2816 : B2816.tree = HexagonCover.NBand.M7300_7500.SplitData.node2816 := by
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

def B2815 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B2816, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq2815 : B2815.tree = HexagonCover.NBand.M7300_7500.SplitData.node2815 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2816
  · rfl
  · rfl

def B2814 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B2815, (.leaf 6 (Common.fact 897).pointIds 897)]
theorem treeEq2814 : B2814.tree = HexagonCover.NBand.M7300_7500.SplitData.node2814 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2815
  · rfl

def B2813 : Block := .branch 125 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![B2814, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2813 : B2813.tree = HexagonCover.NBand.M7300_7500.SplitData.node2813 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2814
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2812 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 723).pointIds 723), B2813, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq2812 : B2812.tree = HexagonCover.NBand.M7300_7500.SplitData.node2812 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2813
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2811 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2812]
theorem treeEq2811 : B2811.tree = HexagonCover.NBand.M7300_7500.SplitData.node2811 := by
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
  · exact treeEq2812

def B2810 : Block := .branch 169 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B2811, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2810 : B2810.tree = HexagonCover.NBand.M7300_7500.SplitData.node2810 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2811
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2809 : Block := .branch 170 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2810, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2809 : B2809.tree = HexagonCover.NBand.M7300_7500.SplitData.node2809 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2810
  · rfl

def B2808 : Block := .branch 171 ![2475880078570760549798248833, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2809, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq2808 : B2808.tree = HexagonCover.NBand.M7300_7500.SplitData.node2808 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2809
  · rfl
  · rfl

def B2786 : Block := .branch 68 ![10384596192949733827821542456689025, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), Tip2688_2787, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B2808]
theorem treeEq2786 : B2786.tree = HexagonCover.NBand.M7300_7500.SplitData.node2786 := by
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
  · exact treeEq2808

def B2785 : Block := .branch 91 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2786, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq2785 : B2785.tree = HexagonCover.NBand.M7300_7500.SplitData.node2785 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2786
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2784 : Block := .branch 113 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B2785, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq2784 : B2784.tree = HexagonCover.NBand.M7300_7500.SplitData.node2784 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2785
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2691 : Block := .branch 76 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip2688_2692, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B2784]
theorem treeEq2691 : B2691.tree = HexagonCover.NBand.M7300_7500.SplitData.node2691 := by
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
  · exact treeEq2784

def B2690 : Block := .branch 74 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), B2691, Tip2688_2817, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq2690 : B2690.tree = HexagonCover.NBand.M7300_7500.SplitData.node2690 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2691
  · rfl
  · rfl
  · rfl
  · rfl

def B2689 : Block := .branch 73 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), B2690, Tip2688_2833, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq2689 : B2689.tree = HexagonCover.NBand.M7300_7500.SplitData.node2689 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2690
  · rfl
  · rfl
  · rfl
  · rfl

def B2688 : Block := .branch 72 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), B2689, Tip2688_2849, (.leaf 4 (Common.fact 380).pointIds 380), (.leaf 5 (Common.fact 381).pointIds 381), (.leaf 6 (Common.fact 382).pointIds 382)]
theorem treeEq2688 : B2688.tree = HexagonCover.NBand.M7300_7500.SplitData.node2688 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2689
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2688 : B2688.accepted = true := by decide +kernel
theorem checked2688 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2688 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2688]
  exact B2688.sound accepted2688
#print axioms checked2688

def Tip2687_2688 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2688 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2688
def B2880 : Block := .branch 125 ![1122433257470133446372726810060932987626252522226049, 1538, 6148, 24584, 98320, 1730417938599789055153162841936079095272624131276832, 21778071483257283796722853571625821405248] ![(.leaf 0 (Common.fact 909).pointIds 909), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 836).pointIds 836), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2880 : B2880.tree = HexagonCover.NBand.M7300_7500.SplitData.node2880 := by
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

def B2879 : Block := .branch 168 ![748288838313422299312583492885564534594333791224193, 1237940039285381374410753538, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![B2880, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq2879 : B2879.tree = HexagonCover.NBand.M7300_7500.SplitData.node2879 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2880
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2878 : Block := .branch 90 ![748288838313422299312583492885564534594333791224193, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294132123885683768185146835008] ![(.leaf 0 (Common.fact 906).pointIds 906), B2879, (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 907).pointIds 907)]
theorem treeEq2878 : B2878.tree = HexagonCover.NBand.M7300_7500.SplitData.node2878 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2879
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2877 : Block := .branch 169 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1730417938599789055153162841936079095272624131276832, 14615016395087100665294286866390594440719509225536] ![B2878, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 905).pointIds 905), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2877 : B2877.tree = HexagonCover.NBand.M7300_7500.SplitData.node2877 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2878
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2876 : Block := .branch 170 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156072452721829093742851929861917165008415981584, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 837).pointIds 837), B2877, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2876 : B2876.tree = HexagonCover.NBand.M7300_7500.SplitData.node2876 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2877
  · rfl

def B2875 : Block := .branch 171 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 20461022944410712338109026197255726519343239397440] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2876, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 904).pointIds 904)]
theorem treeEq2875 : B2875.tree = HexagonCover.NBand.M7300_7500.SplitData.node2875 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2876
  · rfl
  · rfl

def B2874 : Block := .branch 162 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 838).pointIds 838), (.leaf 5 (Common.fact 339).pointIds 339), B2875]
theorem treeEq2874 : B2874.tree = HexagonCover.NBand.M7300_7500.SplitData.node2874 := by
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
  · exact treeEq2875

def B2873 : Block := .branch 78 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 134).pointIds 134), B2874, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), (.leaf 6 (Common.fact 903).pointIds 903)]
theorem treeEq2873 : B2873.tree = HexagonCover.NBand.M7300_7500.SplitData.node2873 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2874
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2872 : Block := .branch 68 ![5192296858534827628530496329220481, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![(.leaf 0 (Common.fact 901).pointIds 901), B2873, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq2872 : B2872.tree = HexagonCover.NBand.M7300_7500.SplitData.node2872 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2873
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2871 : Block := .branch 112 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 14615016395087100665294286866390594440719509225536] ![B2872, (.leaf 1 (Common.fact 421).pointIds 421), (.leaf 2 (Common.fact 422).pointIds 422), (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 900).pointIds 900)]
theorem treeEq2871 : B2871.tree = HexagonCover.NBand.M7300_7500.SplitData.node2871 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2872
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2870 : Block := .branch 163 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 233840261972944466912589573234605283144949207269408, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 570).pointIds 570), (.leaf 5 (Common.fact 248).pointIds 248), B2871]
theorem treeEq2870 : B2870.tree = HexagonCover.NBand.M7300_7500.SplitData.node2870 := by
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
  · exact treeEq2871

def B2869 : Block := .branch 165 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 187072209578355573530071658587684226515959365894176, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 834).pointIds 834), B2870, (.leaf 0 [] 0)]
theorem treeEq2869 : B2869.tree = HexagonCover.NBand.M7300_7500.SplitData.node2869 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2870
  · rfl

def B2868 : Block := .branch 167 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 719199032652612596314526914292909658567966736, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 513).pointIds 513), (.leaf 1 (Common.fact 514).pointIds 514), (.leaf 2 (Common.fact 515).pointIds 515), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 833).pointIds 833), B2869, (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq2868 : B2868.tree = HexagonCover.NBand.M7300_7500.SplitData.node2868 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2869
  · rfl

def B2867 : Block := .branch 142 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B2868, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq2867 : B2867.tree = HexagonCover.NBand.M7300_7500.SplitData.node2867 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2868
  · rfl
  · rfl

def B2866 : Block := .branch 144 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 128).pointIds 128), (.leaf 1 (Common.fact 129).pointIds 129), (.leaf 2 (Common.fact 130).pointIds 130), (.leaf 3 (Common.fact 131).pointIds 131), (.leaf 4 (Common.fact 132).pointIds 132), B2867, (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq2866 : B2866.tree = HexagonCover.NBand.M7300_7500.SplitData.node2866 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2867
  · rfl

def B2865 : Block := .branch 161 ![385, 144116287587485186, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 861).pointIds 861), (.leaf 3 (Common.fact 842).pointIds 842), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B2866]
theorem treeEq2865 : B2865.tree = HexagonCover.NBand.M7300_7500.SplitData.node2865 := by
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
  · exact treeEq2866

def B2687 : Block := .branch 71 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip2687_2688, B2865, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq2687 : B2687.tree = HexagonCover.NBand.M7300_7500.SplitData.node2687 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2865
  · rfl
  · rfl
  · rfl

theorem accepted2687 : B2687.accepted = true := by decide +kernel
theorem checked2687 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2687 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2687]
  exact B2687.sound accepted2687
#print axioms checked2687

def Tip2685_2687 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2687 ![385, 147718068877263898114, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked2687
def B2890 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq2890 : B2890.tree = HexagonCover.NBand.M7300_7500.SplitData.node2890 := by
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

def B2889 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 23384026219072518174517324317865330546450955239488] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B2890, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 911).pointIds 911)]
theorem treeEq2889 : B2889.tree = HexagonCover.NBand.M7300_7500.SplitData.node2889 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2890
  · rfl
  · rfl

def B2888 : Block := .branch 90 ![748288838313422294120286634350736906063837462004097, 374144419156711147060143317175958748843376948282882, 6148, 24584, 98320, 393248, 23384026219072518174516086377826045166176056115264] ![(.leaf 0 (Common.fact 873).pointIds 873), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), B2889]
theorem treeEq2888 : B2888.tree = HexagonCover.NBand.M7300_7500.SplitData.node2888 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2889

def B2887 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 590295811458217281026, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377826045166176056115264] ![(.leaf 0 (Common.fact 605).pointIds 605), B2888, (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq2887 : B2887.tree = HexagonCover.NBand.M7300_7500.SplitData.node2887 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2888
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2886 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 590295811458217281026, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862835866511244780896320] ![B2887, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq2886 : B2886.tree = HexagonCover.NBand.M7300_7500.SplitData.node2886 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2887
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2885 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862835866511244780896320] ![(.leaf 0 (Common.fact 753).pointIds 753), B2886, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq2885 : B2885.tree = HexagonCover.NBand.M7300_7500.SplitData.node2885 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2886
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2884 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2885]
theorem treeEq2884 : B2884.tree = HexagonCover.NBand.M7300_7500.SplitData.node2884 := by
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
  · exact treeEq2885

def B2883 : Block := .branch 169 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539375338196749860208704] ![B2884, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2883 : B2883.tree = HexagonCover.NBand.M7300_7500.SplitData.node2883 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2884
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2882 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2883, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2882 : B2882.tree = HexagonCover.NBand.M7300_7500.SplitData.node2882 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2883
  · rfl

def B2881 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539375338196749860208704] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2882, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq2881 : B2881.tree = HexagonCover.NBand.M7300_7500.SplitData.node2881 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2882
  · rfl
  · rfl

def B2686 : Block := .branch 67 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 198).pointIds 198), Tip2685_2687, (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), (.leaf 4 (Common.fact 201).pointIds 201), (.leaf 5 (Common.fact 202).pointIds 202), B2881]
theorem treeEq2686 : B2686.tree = HexagonCover.NBand.M7300_7500.SplitData.node2686 := by
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
  · exact treeEq2881

def B2896 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 847).pointIds 847), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2896 : B2896.tree = HexagonCover.NBand.M7300_7500.SplitData.node2896 := by
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

def B2895 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B2896, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq2895 : B2895.tree = HexagonCover.NBand.M7300_7500.SplitData.node2895 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2896
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2894 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2895]
theorem treeEq2894 : B2894.tree = HexagonCover.NBand.M7300_7500.SplitData.node2894 := by
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
  · exact treeEq2895

def B2893 : Block := .branch 169 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539264657732307602899008] ![B2894, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2893 : B2893.tree = HexagonCover.NBand.M7300_7500.SplitData.node2893 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2894
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2892 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2893, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2892 : B2892.tree = HexagonCover.NBand.M7300_7500.SplitData.node2892 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2893
  · rfl

def B2891 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2892, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2891 : B2891.tree = HexagonCover.NBand.M7300_7500.SplitData.node2891 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2892
  · rfl
  · rfl

def B2685 : Block := .branch 65 ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), B2686, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B2891]
theorem treeEq2685 : B2685.tree = HexagonCover.NBand.M7300_7500.SplitData.node2685 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2686
  · rfl
  · rfl
  · rfl
  · exact treeEq2891

theorem accepted2685 : B2685.accepted = true := by decide +kernel
theorem checked2685 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2685 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 79266848140492005727134572552, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2685]
  exact B2685.sound accepted2685
#print axioms checked2685

def Tip2498_2509 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node2509 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] HexagonCover.NBand.M7300_7500.SplitTree.Run0037.checked2509
def B2502 : Block := .branch 91 ![288230376151712129, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2502 : B2502.tree = HexagonCover.NBand.M7300_7500.SplitData.node2502 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2501 : Block := .branch 171 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2502]
theorem treeEq2501 : B2501.tree = HexagonCover.NBand.M7300_7500.SplitData.node2501 := by
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
  · exact treeEq2502

def B2500 : Block := .branch 170 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2501, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2500 : B2500.tree = HexagonCover.NBand.M7300_7500.SplitData.node2500 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2501
  · rfl
  · rfl

def B2499 : Block := .branch 169 ![288230376151712129, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 800).pointIds 800), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2500, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2499 : B2499.tree = HexagonCover.NBand.M7300_7500.SplitData.node2499 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2500
  · rfl

def B2507 : Block := .branch 91 ![576460752303423873, 1538, 6148, 24584, 98320, 393248, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 809).pointIds 809), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq2507 : B2507.tree = HexagonCover.NBand.M7300_7500.SplitData.node2507 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2506 : Block := .branch 171 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B2507]
theorem treeEq2506 : B2506.tree = HexagonCover.NBand.M7300_7500.SplitData.node2506 := by
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
  · exact treeEq2507

def B2505 : Block := .branch 170 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), B2506, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2505 : B2505.tree = HexagonCover.NBand.M7300_7500.SplitData.node2505 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2506
  · rfl
  · rfl

def B2504 : Block := .branch 169 ![576460752303423873, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 808).pointIds 808), (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), B2505, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2504 : B2504.tree = HexagonCover.NBand.M7300_7500.SplitData.node2504 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2505
  · rfl

def B2674 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 753).pointIds 753), (.leaf 1 (Common.fact 847).pointIds 847), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq2674 : B2674.tree = HexagonCover.NBand.M7300_7500.SplitData.node2674 := by
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

def B2673 : Block := .branch 159 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 846).pointIds 846), B2674, (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 796).pointIds 796)]
theorem treeEq2673 : B2673.tree = HexagonCover.NBand.M7300_7500.SplitData.node2673 := by
  change Tree.branch (159 : Fin 172) _ = Tree.branch (159 : Fin 172) _
  apply congrArg (Tree.branch (159 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2674
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2672 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1099511629314, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2673]
theorem treeEq2672 : B2672.tree = HexagonCover.NBand.M7300_7500.SplitData.node2672 := by
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
  · exact treeEq2673

def B2671 : Block := .branch 169 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539264657732307602899008] ![B2672, (.leaf 1 (Common.fact 850).pointIds 850), (.leaf 2 (Common.fact 851).pointIds 851), (.leaf 3 (Common.fact 625).pointIds 625), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq2671 : B2671.tree = HexagonCover.NBand.M7300_7500.SplitData.node2671 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2672
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2670 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 853).pointIds 853), (.leaf 3 (Common.fact 623).pointIds 623), (.leaf 4 (Common.fact 655).pointIds 655), B2671, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq2670 : B2670.tree = HexagonCover.NBand.M7300_7500.SplitData.node2670 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2671
  · rfl

def B2669 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539264657732307602899008] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 854).pointIds 854), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 620).pointIds 620), B2670, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq2669 : B2669.tree = HexagonCover.NBand.M7300_7500.SplitData.node2669 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2670
  · rfl
  · rfl

def B2508 : Block := .branch 65 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), Tip2498_2509, (.leaf 3 (Common.fact 118).pointIds 118), (.leaf 4 (Common.fact 119).pointIds 119), (.leaf 5 (Common.fact 120).pointIds 120), B2669]
theorem treeEq2508 : B2508.tree = HexagonCover.NBand.M7300_7500.SplitData.node2508 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2669

def B2503 : Block := .branch 59 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2504, B2508, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq2503 : B2503.tree = HexagonCover.NBand.M7300_7500.SplitData.node2503 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2504
  · exact treeEq2508
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2498 : Block := .branch 58 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![B2499, B2503, (.leaf 2 (Common.fact 158).pointIds 158), (.leaf 3 (Common.fact 159).pointIds 159), (.leaf 4 (Common.fact 160).pointIds 160), (.leaf 5 (Common.fact 161).pointIds 161), (.leaf 6 (Common.fact 162).pointIds 162)]
theorem treeEq2498 : B2498.tree = HexagonCover.NBand.M7300_7500.SplitData.node2498 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq2499
  · exact treeEq2503
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2498 : B2498.accepted = true := by decide +kernel
theorem checked2498 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node2498 (maskNeeds ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq2498]
  exact B2498.sound accepted2498
#print axioms checked2498

end HexagonCover.NBand.M7300_7500.SplitTree.Run0040
