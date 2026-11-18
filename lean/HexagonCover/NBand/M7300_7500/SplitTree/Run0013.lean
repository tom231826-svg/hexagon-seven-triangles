import HexagonCover.NBand.M7300_7500.SplitData
import HexagonCover.NBand.M7300_7500.SplitTree.Run0012
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7300_7500.SplitTree.Run0013
open OwnerTree HexagonCover.NBand.M7300_7500

abbrev Block := Chunk (n := 172) (Certificate := Fin 1033) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0980_0982 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0982 ![2535301200456458802993406411137, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7300_7500.SplitTree.Run0012.checked0982
def B1001 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1001 : B1001.tree = HexagonCover.NBand.M7300_7500.SplitData.node1001 := by
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

def B1000 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665237195014238513204393567241896000] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B1001, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq1000 : B1000.tree = HexagonCover.NBand.M7300_7500.SplitData.node1000 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1001
  · rfl
  · rfl

def B0999 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518177051697063144751361648510894144] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1000]
theorem treeEq0999 : B0999.tree = HexagonCover.NBand.M7300_7500.SplitData.node0999 := by
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
  · exact treeEq1000

def B0998 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518177051697063144751361648510894144] ![B0999, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq0998 : B0998.tree = HexagonCover.NBand.M7300_7500.SplitData.node0998 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0999
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0997 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0998]
theorem treeEq0997 : B0997.tree = HexagonCover.NBand.M7300_7500.SplitData.node0997 := by
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
  · exact treeEq0998

def B0996 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739739684223047153590206528] ![B0997, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0996 : B0996.tree = HexagonCover.NBand.M7300_7500.SplitData.node0996 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0997
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0995 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B0996, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq0995 : B0995.tree = HexagonCover.NBand.M7300_7500.SplitData.node0995 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0996
  · rfl

def B0994 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071485792739739684223047153590206528] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B0995, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 747).pointIds 747)]
theorem treeEq0994 : B0994.tree = HexagonCover.NBand.M7300_7500.SplitData.node0994 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0995
  · rfl
  · rfl

def B0981 : Block := .branch 101 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0980_0982, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0994]
theorem treeEq0981 : B0981.tree = HexagonCover.NBand.M7300_7500.SplitData.node0981 := by
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
  · exact treeEq0994

def B1009 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 21778071483259604934296513659641257263168] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 586).pointIds 586)]
theorem treeEq1009 : B1009.tree = HexagonCover.NBand.M7300_7500.SplitData.node1009 := by
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

def B1008 : Block := .branch 142 ![385, 1538, 6148, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 397528445375783665234661879433125495006054908952640] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), B1009, (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq1008 : B1008.tree = HexagonCover.NBand.M7300_7500.SplitData.node1008 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1009
  · rfl
  · rfl

def B1007 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 23384026219072518174518562257757041974136177950784] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1008]
theorem treeEq1007 : B1007.tree = HexagonCover.NBand.M7300_7500.SplitData.node1007 := by
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
  · exact treeEq1008

def B1006 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 23384026219072518174518871742766863319204902731840] ![B1007, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1006 : B1006.tree = HexagonCover.NBand.M7300_7500.SplitData.node1006 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1007
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1005 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1006]
theorem treeEq1005 : B1005.tree = HexagonCover.NBand.M7300_7500.SplitData.node1005 := by
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
  · exact treeEq1006

def B1004 : Block := .branch 169 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071483259914419306335004709982044224] ![B1005, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1004 : B1004.tree = HexagonCover.NBand.M7300_7500.SplitData.node1004 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1005
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1003 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1004, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1003 : B1003.tree = HexagonCover.NBand.M7300_7500.SplitData.node1003 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1004
  · rfl

def B1002 : Block := .branch 171 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483259914419306335004709982044224] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1003, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq1002 : B1002.tree = HexagonCover.NBand.M7300_7500.SplitData.node1002 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1003
  · rfl
  · rfl

def B0980 : Block := .branch 91 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0981, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), B1002]
theorem treeEq0980 : B0980.tree = HexagonCover.NBand.M7300_7500.SplitData.node0980 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0981
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1002

theorem accepted0980 : B0980.accepted = true := by decide +kernel
theorem checked0980 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0980 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0980]
  exact B0980.sound accepted0980
#print axioms checked0980

def Tip0978_0980 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node0980 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0980
def B1017 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 608).pointIds 608)]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M7300_7500.SplitData.node1017 := by
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

def B1016 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659403553046924245505110704192] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1017, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 606).pointIds 606)]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M7300_7500.SplitData.node1016 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1017
  · rfl
  · rfl

def B1015 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516086377678471213586379702336] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1016]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M7300_7500.SplitData.node1015 := by
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
  · exact treeEq1016

def B1014 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516395862688292558655104483392] ![B1015, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M7300_7500.SplitData.node1014 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1015
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1013 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1014]
theorem treeEq1013 : B1013.tree = HexagonCover.NBand.M7300_7500.SplitData.node1013 := by
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
  · exact treeEq1014

def B1012 : Block := .branch 169 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438539227764244160183795776] ![B1013, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1012 : B1012.tree = HexagonCover.NBand.M7300_7500.SplitData.node1012 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1013
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1011 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1012, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1011 : B1011.tree = HexagonCover.NBand.M7300_7500.SplitData.node1011 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1012
  · rfl

def B1010 : Block := .branch 171 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483258057509247406934297633357888] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1011, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 595).pointIds 595)]
theorem treeEq1010 : B1010.tree = HexagonCover.NBand.M7300_7500.SplitData.node1010 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1011
  · rfl
  · rfl

def B0979 : Block := .branch 89 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 86).pointIds 86), Tip0978_0980, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1010]
theorem treeEq0979 : B0979.tree = HexagonCover.NBand.M7300_7500.SplitData.node0979 := by
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
  · exact treeEq1010

def B1025 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 192).pointIds 192), (.leaf 1 (Common.fact 193).pointIds 193), (.leaf 2 (Common.fact 194).pointIds 194), (.leaf 3 (Common.fact 195).pointIds 195), (.leaf 4 (Common.fact 632).pointIds 632), (.leaf 5 (Common.fact 197).pointIds 197), (.leaf 6 (Common.fact 630).pointIds 630)]
theorem treeEq1025 : B1025.tree = HexagonCover.NBand.M7300_7500.SplitData.node1025 := by
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

def B1024 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659326181794468909237929508928] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1025, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 629).pointIds 629)]
theorem treeEq1024 : B1024.tree = HexagonCover.NBand.M7300_7500.SplitData.node1024 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1025
  · rfl
  · rfl

def B1023 : Block := .branch 168 ![748288838313464829416151751658669827889766433030529, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174516009006426015877319198507072] ![(.leaf 0 (Common.fact 605).pointIds 605), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1024]
theorem treeEq1023 : B1023.tree = HexagonCover.NBand.M7300_7500.SplitData.node1023 := by
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
  · exact treeEq1024

def B1022 : Block := .branch 125 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516318491435837222387923288128] ![B1023, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1022 : B1022.tree = HexagonCover.NBand.M7300_7500.SplitData.node1022 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1023
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1021 : Block := .branch 164 ![748288838313422294120286634350736906063837462004097, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 604).pointIds 604), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1022]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M7300_7500.SplitData.node1021 := by
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
  · exact treeEq1022

def B1020 : Block := .branch 169 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257515910480219580427364991040] ![B1021, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M7300_7500.SplitData.node1020 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1021
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1019 : Block := .branch 170 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1020, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M7300_7500.SplitData.node1019 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1020
  · rfl

def B1018 : Block := .branch 171 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257515910480219580427364991040] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1019, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 622).pointIds 622)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M7300_7500.SplitData.node1018 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1019
  · rfl
  · rfl

def B0978 : Block := .branch 86 ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0979, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B1018]
theorem treeEq0978 : B0978.tree = HexagonCover.NBand.M7300_7500.SplitData.node0978 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0979
  · rfl
  · rfl
  · exact treeEq1018

theorem accepted0978 : B0978.accepted = true := by decide +kernel
theorem checked0978 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node0978 (maskNeeds ![385, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0978]
  exact B0978.sound accepted0978
#print axioms checked0978

def B1059 : Block := .branch 142 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 24114777037737969633617774127089565776794307002432] ![(.leaf 0 (Common.fact 140).pointIds 140), (.leaf 1 (Common.fact 141).pointIds 141), (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 144).pointIds 144), (.leaf 6 (Common.fact 683).pointIds 683)]
theorem treeEq1059 : B1059.tree = HexagonCover.NBand.M7300_7500.SplitData.node1059 := by
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

def B1058 : Block := .branch 159 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 681).pointIds 681), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 226).pointIds 226), (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), B1059]
theorem treeEq1058 : B1058.tree = HexagonCover.NBand.M7300_7500.SplitData.node1058 := by
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
  · exact treeEq1059

def B1057 : Block := .branch 164 ![748288838313422294122821935551193364866830868414849, 737941821641931621890, 6148, 24584, 324518553658426726783156020674576, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1058]
theorem treeEq1057 : B1057.tree = HexagonCover.NBand.M7300_7500.SplitData.node1057 := by
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
  · exact treeEq1058

def B1056 : Block := .branch 169 ![2535301200456458802993406411137, 737941821641931621890, 2398076729582241716228, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1057, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1056 : B1056.tree = HexagonCover.NBand.M7300_7500.SplitData.node1056 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1057
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1055 : Block := .branch 170 ![2535301200456458802993406411137, 737941821641931621890, 2398076729582241716228, 38690348594151003235835912, 713623846353304459082801411451530724212047888, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 679).pointIds 679), B1056, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1055 : B1055.tree = HexagonCover.NBand.M7300_7500.SplitData.node1055 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1056
  · rfl

def B1064 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 2993155353275467248288605152798588189640603112833088] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), (.leaf 3 (Common.fact 774).pointIds 774), (.leaf 4 (Common.fact 658).pointIds 658), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1064 : B1064.tree = HexagonCover.NBand.M7300_7500.SplitData.node1064 := by
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

def B1063 : Block := .branch 171 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 1496577676626844588240573268701473812127674924105744, 393248, 21778071807458615395640565385253264818240] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 656).pointIds 656), B1064]
theorem treeEq1063 : B1063.tree = HexagonCover.NBand.M7300_7500.SplitData.node1063 := by
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
  · exact treeEq1064

def B1062 : Block := .branch 170 ![385, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 42535295865117307932921825928971419680, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), B1063, (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1062 : B1062.tree = HexagonCover.NBand.M7300_7500.SplitData.node1062 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1063
  · rfl
  · rfl

def B1061 : Block := .branch 125 ![374144419156711157447272335445480168895904795853185, 147646011283225970178, 2398076729582241716228, 38690348594151003235835912, 98320, 393248, 21778071807775992273212354753230527791168] ![(.leaf 0 (Common.fact 685).pointIds 685), (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), B1062, (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1061 : B1061.tree = HexagonCover.NBand.M7300_7500.SplitData.node1061 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1062
  · rfl

def B1060 : Block := .branch 168 ![10387129018270111715863986064851329, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071807775992273212354753230527791168] ![B1061, (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq1060 : B1060.tree = HexagonCover.NBand.M7300_7500.SplitData.node1060 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1061
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1054 : Block := .branch 108 ![10387129018270111715863986064851329, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), B1055, (.leaf 5 (Common.fact 308).pointIds 308), B1060]
theorem treeEq1054 : B1054.tree = HexagonCover.NBand.M7300_7500.SplitData.node1054 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1055
  · rfl
  · exact treeEq1060

theorem accepted1054 : B1054.accepted = true := by decide +kernel
theorem checked1054 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1054 (maskNeeds ![10387129018270111715863986064851329, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1054]
  exact B1054.sound accepted1054
#print axioms checked1054

def Tip1052_1054 : Block := .tip HexagonCover.NBand.M7300_7500.SplitData.node1054 ![10387129018270111715863986064851329, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] checked1054
def B1073 : Block := .branch 109 ![385, 1538, 6148, 24584, 2993338040958355539345921998007037159632806839681040, 393248, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 701).pointIds 701), (.leaf 1 (Common.fact 702).pointIds 702), (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1073 : B1073.tree = HexagonCover.NBand.M7300_7500.SplitData.node1073 := by
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

def B1072 : Block := .branch 157 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577687777217187505884839469332948451855677390880, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 175).pointIds 175), (.leaf 1 (Common.fact 176).pointIds 176), (.leaf 2 (Common.fact 177).pointIds 177), (.leaf 3 (Common.fact 178).pointIds 178), B1073, (.leaf 5 (Common.fact 700).pointIds 700), (.leaf 0 [] 0)]
theorem treeEq1072 : B1072.tree = HexagonCover.NBand.M7300_7500.SplitData.node1072 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1073
  · rfl
  · rfl

def B1071 : Block := .branch 143 ![385, 1538, 6148, 24584, 2993155353253689176481146537402947624255349848113168, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 507).pointIds 507), (.leaf 1 (Common.fact 508).pointIds 508), (.leaf 2 (Common.fact 509).pointIds 509), (.leaf 3 (Common.fact 510).pointIds 510), (.leaf 4 (Common.fact 698).pointIds 698), B1072, (.leaf 6 (Common.fact 699).pointIds 699)]
theorem treeEq1071 : B1071.tree = HexagonCover.NBand.M7300_7500.SplitData.node1071 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1072
  · rfl

def B1070 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792275587727354755464826454080] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1071]
theorem treeEq1070 : B1070.tree = HexagonCover.NBand.M7300_7500.SplitData.node1070 := by
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
  · exact treeEq1071

def B1069 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![B1070, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1069 : B1069.tree = HexagonCover.NBand.M7300_7500.SplitData.node1069 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1070
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1068 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792585072737176100533551235136] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1069]
theorem treeEq1068 : B1068.tree = HexagonCover.NBand.M7300_7500.SplitData.node1068 := by
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
  · exact treeEq1069

def B1067 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 1496577676626844588240573268701473812127674924400672, 21778071485792739815242086773067913625664] ![B1068, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1067 : B1067.tree = HexagonCover.NBand.M7300_7500.SplitData.node1067 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1068
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1066 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1067, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1066 : B1066.tree = HexagonCover.NBand.M7300_7500.SplitData.node1066 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1067
  · rfl

def B1065 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071485792739815242086773067913625664] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1066, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 695).pointIds 695)]
theorem treeEq1065 : B1065.tree = HexagonCover.NBand.M7300_7500.SplitData.node1065 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1066
  · rfl
  · rfl

def B1053 : Block := .branch 101 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![Tip1052_1054, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B1065]
theorem treeEq1053 : B1053.tree = HexagonCover.NBand.M7300_7500.SplitData.node1053 := by
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
  · exact treeEq1065

def B1081 : Block := .branch 122 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 709).pointIds 709), (.leaf 1 (Common.fact 710).pointIds 710), (.leaf 2 (Common.fact 711).pointIds 711), (.leaf 3 (Common.fact 712).pointIds 712), (.leaf 4 (Common.fact 713).pointIds 713), (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M7300_7500.SplitData.node1081 := by
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

def B1080 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 397528445375783665234659248886099877298885071732800] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B1081, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M7300_7500.SplitData.node1080 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1081
  · rfl
  · rfl

def B1079 : Block := .branch 168 ![748288838313464829416154227538748398650316231278977, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 23384026219072518174515931710731424266966340730944] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 370).pointIds 370), (.leaf 2 (Common.fact 371).pointIds 371), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), B1080]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M7300_7500.SplitData.node1079 := by
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
  · exact treeEq1080

def B1078 : Block := .branch 125 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 23384026219072518174516241195741245612035065512000] ![B1079, (.leaf 1 (Common.fact 170).pointIds 170), (.leaf 2 (Common.fact 171).pointIds 171), (.leaf 3 (Common.fact 172).pointIds 172), (.leaf 4 (Common.fact 173).pointIds 173), (.leaf 5 (Common.fact 455).pointIds 455), (.leaf 6 (Common.fact 174).pointIds 174)]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M7300_7500.SplitData.node1078 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1079
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1077 : Block := .branch 164 ![748288838313422294120289110230815476824387260252545, 360289069701268994, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257283872280717297540144824384] ![(.leaf 0 (Common.fact 696).pointIds 696), (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1078]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M7300_7500.SplitData.node1077 := by
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
  · exact treeEq1078

def B1076 : Block := .branch 169 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 21778071483257438614785627970074507214912] ![B1077, (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 770).pointIds 770), (.leaf 3 (Common.fact 771).pointIds 771), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M7300_7500.SplitData.node1076 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq1077
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1075 : Block := .branch 170 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 768).pointIds 768), (.leaf 3 (Common.fact 769).pointIds 769), (.leaf 4 (Common.fact 655).pointIds 655), B1076, (.leaf 6 (Common.fact 730).pointIds 730)]
theorem treeEq1075 : B1075.tree = HexagonCover.NBand.M7300_7500.SplitData.node1075 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1076
  · rfl

def B1074 : Block := .branch 171 ![2475880078570760549798248833, 147934241659377681922, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 742).pointIds 742), (.leaf 1 (Common.fact 653).pointIds 653), (.leaf 2 (Common.fact 772).pointIds 772), (.leaf 3 (Common.fact 773).pointIds 773), B1075, (.leaf 5 (Common.fact 656).pointIds 656), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq1074 : B1074.tree = HexagonCover.NBand.M7300_7500.SplitData.node1074 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1075
  · rfl
  · rfl

def B1052 : Block := .branch 89 ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912] ![(.leaf 0 (Common.fact 86).pointIds 86), B1053, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B1074]
theorem treeEq1052 : B1052.tree = HexagonCover.NBand.M7300_7500.SplitData.node1052 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1053
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1074

theorem accepted1052 : B1052.accepted = true := by decide +kernel
theorem checked1052 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7300_7500.SplitData.node1052 (maskNeeds ![10384596192949733827821542456689025, 738230052018083333634, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071483257438614785627970074507214912]) := by
  rw [← treeEq1052]
  exact B1052.sound accepted1052
#print axioms checked1052

end HexagonCover.NBand.M7300_7500.SplitTree.Run0013
