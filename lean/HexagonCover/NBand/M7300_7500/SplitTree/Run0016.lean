import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0012
import HexagonCover.NBand.M7300_7500.SplitTree.Run0014
import HexagonCover.NBand.M7300_7500.SplitTree.Run0015
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0016
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip1107_1109 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1109 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0015.checked1109
def B1164 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1164 : B1164.tree = HexagonCover.NBand.M7300_7500.SplitData.node1164 := by
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

def B1163 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1164, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 631).pointIds 631)]
theorem treeEq1163 : B1163.tree = HexagonCover.NBand.M7300_7500.SplitData.node1163 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1164
  · rfl
  · rfl

def B1162 : Block := .branch 125 ![385, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B1163, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1162 : B1162.tree = HexagonCover.NBand.M7300_7500.SplitData.node1162 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1163
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1161 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 753).pointIds 753), B1162, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq1161 : B1161.tree = HexagonCover.NBand.M7300_7500.SplitData.node1161 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1162
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1160 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1161]
theorem treeEq1160 : B1160.tree = HexagonCover.NBand.M7300_7500.SplitData.node1160 := by
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
  · exact treeEq1161

def B1159 : Block := .branch 169 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257439748153583858789358501952] ![B1160, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1159 : B1159.tree = HexagonCover.NBand.M7300_7500.SplitData.node1159 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1160
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1158 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1159, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1158 : B1158.tree = HexagonCover.NBand.M7300_7500.SplitData.node1158 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1159
  · rfl

def B1157 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257439748153583858789358501952] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1158, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 752).pointIds 752)]
theorem treeEq1157 : B1157.tree = HexagonCover.NBand.M7300_7500.SplitData.node1157 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1158
  · rfl
  · rfl

def B1108 : Block := .branch 80 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip1107_1109, (.leaf 1 (Common.fact 398).pointIds 398), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), B1157]
theorem treeEq1108 : B1108.tree = HexagonCover.NBand.M7300_7500.SplitData.node1108 := by
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
  · exact treeEq1157

def B1172 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq1172 : B1172.tree = HexagonCover.NBand.M7300_7500.SplitData.node1172 := by
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

def B1171 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403855278379149162404380736] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1172, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq1171 : B1171.tree = HexagonCover.NBand.M7300_7500.SplitData.node1171 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1172
  · rfl
  · rfl

def B1170 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086679909926117243673378880] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1171]
theorem treeEq1170 : B1170.tree = HexagonCover.NBand.M7300_7500.SplitData.node1170 := by
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
  · exact treeEq1171

def B1169 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516396164919747462312398159936] ![B1170, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1169 : B1169.tree = HexagonCover.NBand.M7300_7500.SplitData.node1169 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1170
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1168 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1169]
theorem treeEq1168 : B1168.tree = HexagonCover.NBand.M7300_7500.SplitData.node1168 := by
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
  · exact treeEq1169

def B1167 : Block := .branch 169 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438841459219147817477472320] ![B1168, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1167 : B1167.tree = HexagonCover.NBand.M7300_7500.SplitData.node1167 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1168
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1166 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1167, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1166 : B1166.tree = HexagonCover.NBand.M7300_7500.SplitData.node1166 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1167
  · rfl

def B1165 : Block := .branch 171 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438841459219147817477472320] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1166, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq1165 : B1165.tree = HexagonCover.NBand.M7300_7500.SplitData.node1165 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1166
  · rfl
  · rfl

def B1107 : Block := .branch 78 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 134).pointIds 134), B1108, (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), (.leaf 5 (Common.fact 139).pointIds 139), B1165]
theorem treeEq1107 : B1107.tree = HexagonCover.NBand.M7300_7500.SplitData.node1107 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1108
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1165

theorem accepted1107 : B1107.accepted = true := by decide +kernel
theorem checked1107 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1107 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq1107]
  exact B1107.sound accepted1107
#print axioms checked1107

def Tip0975_1050 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1050 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0014.checked1050
def Tip0975_0976 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0976 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0014.checked0976
def B1049 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq1049 : B1049.tree = HexagonCover.NBand.M7300_7500.SplitData.node1049 := by
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

def B1048 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1049]
theorem treeEq1048 : B1048.tree = HexagonCover.NBand.M7300_7500.SplitData.node1048 := by
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
  · exact treeEq1049

def B1047 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B1048, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1047 : B1047.tree = HexagonCover.NBand.M7300_7500.SplitData.node1047 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1048
  · rfl
  · rfl

def B1046 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), B1047, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1046 : B1046.tree = HexagonCover.NBand.M7300_7500.SplitData.node1046 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1047
  · rfl

def B1045 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1046, Tip0975_1050, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1045 : B1045.tree = HexagonCover.NBand.M7300_7500.SplitData.node1045 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1046
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1105 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1105 : B1105.tree = HexagonCover.NBand.M7300_7500.SplitData.node1105 := by
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

def B1104 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B1105, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1104 : B1104.tree = HexagonCover.NBand.M7300_7500.SplitData.node1104 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1105
  · rfl
  · rfl

def B1103 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1104]
theorem treeEq1103 : B1103.tree = HexagonCover.NBand.M7300_7500.SplitData.node1103 := by
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
  · exact treeEq1104

def B1102 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B1103, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1102 : B1102.tree = HexagonCover.NBand.M7300_7500.SplitData.node1102 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1103
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1101 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B1102, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1101 : B1101.tree = HexagonCover.NBand.M7300_7500.SplitData.node1101 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1102
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1100 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1101]
theorem treeEq1100 : B1100.tree = HexagonCover.NBand.M7300_7500.SplitData.node1100 := by
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
  · exact treeEq1101

def B1099 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B1100, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1099 : B1099.tree = HexagonCover.NBand.M7300_7500.SplitData.node1099 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1100
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1098 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1099, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1098 : B1098.tree = HexagonCover.NBand.M7300_7500.SplitData.node1098 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1099
  · rfl

def B1097 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1098, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq1097 : B1097.tree = HexagonCover.NBand.M7300_7500.SplitData.node1097 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1098
  · rfl
  · rfl

def B1044 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B1045, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B1097]
theorem treeEq1044 : B1044.tree = HexagonCover.NBand.M7300_7500.SplitData.node1044 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1045
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1097

def B1043 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1044, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq1043 : B1043.tree = HexagonCover.NBand.M7300_7500.SplitData.node1043 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1044
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1042 : Block := .branch 113 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1043, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1042 : B1042.tree = HexagonCover.NBand.M7300_7500.SplitData.node1042 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1043
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0975 : Block := .branch 76 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0975_0976, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B1042]
theorem treeEq0975 : B0975.tree = HexagonCover.NBand.M7300_7500.SplitData.node0975 := by
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
  · exact treeEq1042

theorem accepted0975 : B0975.accepted = true := by decide +kernel
theorem checked0975 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0975 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0975]
  exact B0975.sound accepted0975
#print axioms checked0975

def Tip0711_0918 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0918 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0012.checked0918
def Tip0711_0844 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0844 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0012.checked0844
def Tip0711_0712 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0712 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0012.checked0712
def B0917 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M7300_7500.SplitData.node0917 := by
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

def B0916 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B0917]
theorem treeEq0916 : B0916.tree = HexagonCover.NBand.M7300_7500.SplitData.node0916 := by
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
  · exact treeEq0917

def B0915 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B0916, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0915 : B0915.tree = HexagonCover.NBand.M7300_7500.SplitData.node0915 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0916
  · rfl
  · rfl

def B0914 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), B0915, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0914 : B0914.tree = HexagonCover.NBand.M7300_7500.SplitData.node0914 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0915
  · rfl

def B0913 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0914, Tip0711_0918, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0913 : B0913.tree = HexagonCover.NBand.M7300_7500.SplitData.node0913 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0973 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0973 : B0973.tree = HexagonCover.NBand.M7300_7500.SplitData.node0973 := by
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

def B0972 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B0973, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0972 : B0972.tree = HexagonCover.NBand.M7300_7500.SplitData.node0972 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0973
  · rfl
  · rfl

def B0971 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B0972]
theorem treeEq0971 : B0971.tree = HexagonCover.NBand.M7300_7500.SplitData.node0971 := by
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
  · exact treeEq0972

def B0970 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B0971, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0970 : B0970.tree = HexagonCover.NBand.M7300_7500.SplitData.node0970 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0971
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0969 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B0970, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0969 : B0969.tree = HexagonCover.NBand.M7300_7500.SplitData.node0969 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0970
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0968 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0969]
theorem treeEq0968 : B0968.tree = HexagonCover.NBand.M7300_7500.SplitData.node0968 := by
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
  · exact treeEq0969

def B0967 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B0968, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0967 : B0967.tree = HexagonCover.NBand.M7300_7500.SplitData.node0967 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0968
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0966 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0967, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0966 : B0966.tree = HexagonCover.NBand.M7300_7500.SplitData.node0966 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0967
  · rfl

def B0965 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0966, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq0965 : B0965.tree = HexagonCover.NBand.M7300_7500.SplitData.node0965 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0966
  · rfl
  · rfl

def B0912 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B0913, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B0965]
theorem treeEq0912 : B0912.tree = HexagonCover.NBand.M7300_7500.SplitData.node0912 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0913
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0965

def B0911 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0912, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq0911 : B0911.tree = HexagonCover.NBand.M7300_7500.SplitData.node0911 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0912
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0910 : Block := .branch 113 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B0911, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq0910 : B0910.tree = HexagonCover.NBand.M7300_7500.SplitData.node0910 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0911
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0843 : Block := .branch 76 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0711_0844, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B0910]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M7300_7500.SplitData.node0843 := by
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
  · exact treeEq0910

def B0711 : Block := .branch 74 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0711_0712, B0843, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M7300_7500.SplitData.node0711 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl
  · rfl
  · rfl

theorem accepted0711 : B0711.accepted = true := by decide +kernel
theorem checked0711 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0711 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq0711]
  exact B0711.sound accepted0711
#print axioms checked0711

def Tip0710_1181 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1181 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] HexagonCover.NBand.M7300_7500.SplitTree.Run0015.checked1181
def Tip0710_1107 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1107 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked1107
def Tip0710_0975 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0975 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0975
def Tip0710_0711 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0711 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] checked0711
def B1180 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467247964403511790218520207821268058176] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq1180 : B1180.tree = HexagonCover.NBand.M7300_7500.SplitData.node1180 := by
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

def B1179 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1180]
theorem treeEq1179 : B1179.tree = HexagonCover.NBand.M7300_7500.SplitData.node1179 := by
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
  · exact treeEq1180

def B1178 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 748288838313422294120286634350736906063837462396960, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B1179, (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1178 : B1178.tree = HexagonCover.NBand.M7300_7500.SplitData.node1178 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1179
  · rfl
  · rfl

def B1177 : Block := .branch 169 ![10384593717070245552871351364092289, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), B1178, (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1177 : B1177.tree = HexagonCover.NBand.M7300_7500.SplitData.node1177 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1178
  · rfl

def B1176 : Block := .branch 69 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1177, Tip0710_1181, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1176 : B1176.tree = HexagonCover.NBand.M7300_7500.SplitData.node1176 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1177
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1236 : Block := .branch 109 ![385, 1538, 6148, 24584, 5846006549323611672814739330865132078623730270224, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 759).pointIds 759), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq1236 : B1236.tree = HexagonCover.NBand.M7300_7500.SplitData.node1236 := by
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

def B1235 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 98320, 393248, 397528445375783665234659248886395025204064424558656] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), B1236, (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq1235 : B1235.tree = HexagonCover.NBand.M7300_7500.SplitData.node1235 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1236
  · rfl
  · rfl

def B1234 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931711026572172145693556800] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1235]
theorem treeEq1234 : B1234.tree = HexagonCover.NBand.M7300_7500.SplitData.node1234 := by
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
  · exact treeEq1235

def B1233 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![B1234, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1233 : B1233.tree = HexagonCover.NBand.M7300_7500.SplitData.node1233 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1234
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1232 : Block := .branch 69 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241196036393517214418337856] ![(.leaf 0 (Common.fact 723).pointIds 723), B1233, (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 415).pointIds 415), (.leaf 4 (Common.fact 416).pointIds 416), (.leaf 5 (Common.fact 417).pointIds 417), (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq1232 : B1232.tree = HexagonCover.NBand.M7300_7500.SplitData.node1232 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1233
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1231 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872575865202719497650240] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1232]
theorem treeEq1231 : B1231.tree = HexagonCover.NBand.M7300_7500.SplitData.node1231 := by
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
  · exact treeEq1232

def B1230 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438615080775875253860040768] ![B1231, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1230 : B1230.tree = HexagonCover.NBand.M7300_7500.SplitData.node1230 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1231
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1229 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1230, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1229 : B1229.tree = HexagonCover.NBand.M7300_7500.SplitData.node1229 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1230
  · rfl

def B1228 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438615080775875253860040768] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1229, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 722).pointIds 722)]
theorem treeEq1228 : B1228.tree = HexagonCover.NBand.M7300_7500.SplitData.node1228 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1229
  · rfl
  · rfl

def B1175 : Block := .branch 68 ![10384596192949733827821542456689025, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 637).pointIds 637), B1176, (.leaf 2 (Common.fact 638).pointIds 638), (.leaf 3 (Common.fact 639).pointIds 639), (.leaf 4 (Common.fact 640).pointIds 640), (.leaf 5 (Common.fact 641).pointIds 641), B1228]
theorem treeEq1175 : B1175.tree = HexagonCover.NBand.M7300_7500.SplitData.node1175 := by
  change Tree.branch (68 : Fin 172) _ = Tree.branch (68 : Fin 172) _
  apply congrArg (Tree.branch (68 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1176
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1228

def B1174 : Block := .branch 91 ![10384593717069655257060992658440577, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1175, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq1174 : B1174.tree = HexagonCover.NBand.M7300_7500.SplitData.node1174 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1175
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1173 : Block := .branch 113 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![B1174, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq1173 : B1173.tree = HexagonCover.NBand.M7300_7500.SplitData.node1173 := by
  change Tree.branch (113 : Fin 172) _ = Tree.branch (113 : Fin 172) _
  apply congrArg (Tree.branch (113 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1174
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1106 : Block := .branch 76 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0710_1107, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), B1173]
theorem treeEq1106 : B1106.tree = HexagonCover.NBand.M7300_7500.SplitData.node1106 := by
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
  · exact treeEq1173

def B0974 : Block := .branch 74 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0710_0975, B1106, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0974 : B0974.tree = HexagonCover.NBand.M7300_7500.SplitData.node0974 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1106
  · rfl
  · rfl
  · rfl

def B0710 : Block := .branch 73 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0710_0711, B0974, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M7300_7500.SplitData.node0710 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0974
  · rfl
  · rfl
  · rfl

theorem accepted0710 : B0710.accepted = true := by decide +kernel
theorem checked0710 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0710 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483891263839341878944908535398464]) := by
  rw [← treeEq0710]
  exact B0710.sound accepted0710
#print axioms checked0710

end HexagonCover.NBand.M7300_7500.SplitTree.Run0016
