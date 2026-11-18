import HexagonCover.NBand.M6900_7100.SplitData
import HexagonCover.NBand.M6900_7100.SplitTree.Run0022
import HexagonCover.NBand.M6900_7100.SplitTree.Run0023
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6900_7100.SplitTree.Run0024
open OwnerTree HexagonCover.NBand.M6900_7100

abbrev Block := Chunk (n := 173) (Certificate := Fin 1199) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip1805_1807 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1807 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] HexagonCover.NBand.M6900_7100.SplitTree.Run0023.checked1807
def B1865 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq1865 : B1865.tree = HexagonCover.NBand.M6900_7100.SplitData.node1865 := by
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

def B1864 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543608738007802016308882047040] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1865, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 703).pointIds 703)]
theorem treeEq1864 : B1864.tree = HexagonCover.NBand.M6900_7100.SplitData.node1864 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1865
  · rfl
  · rfl

def B1863 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1864]
theorem treeEq1863 : B1863.tree = HexagonCover.NBand.M6900_7100.SplitData.node1863 := by
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
  · exact treeEq1864

def B1862 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257438614785627970074507214912] ![B1863, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1862 : B1862.tree = HexagonCover.NBand.M6900_7100.SplitData.node1862 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1863
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1861 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483258057584805270660211956777024] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1862, (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq1861 : B1861.tree = HexagonCover.NBand.M6900_7100.SplitData.node1861 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1862
  · rfl

def B1860 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543401374760173723692130687778880] ![B1861, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1860 : B1860.tree = HexagonCover.NBand.M6900_7100.SplitData.node1860 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1861
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1859 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1860, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1859 : B1859.tree = HexagonCover.NBand.M6900_7100.SplitData.node1859 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1860
  · rfl

def B1858 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543401374760173723692130687778880] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1859, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 700).pointIds 700)]
theorem treeEq1858 : B1858.tree = HexagonCover.NBand.M6900_7100.SplitData.node1858 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1859
  · rfl
  · rfl

def B1806 : Block := .branch 89 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 104).pointIds 104), Tip1805_1807, (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), (.leaf 4 (Common.fact 108).pointIds 108), (.leaf 5 (Common.fact 109).pointIds 109), B1858]
theorem treeEq1806 : B1806.tree = HexagonCover.NBand.M6900_7100.SplitData.node1806 := by
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
  · exact treeEq1858

def B1873 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq1873 : B1873.tree = HexagonCover.NBand.M6900_7100.SplitData.node1873 := by
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

def B1872 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 748288838335200365603543686109260257352576063242304] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1873, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq1872 : B1872.tree = HexagonCover.NBand.M6900_7100.SplitData.node1872 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1873
  · rfl
  · rfl

def B1871 : Block := .branch 169 ![93536104789220322060903422481853605844458452025729, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257051758523351288738601238592] ![(.leaf 0 (Common.fact 702).pointIds 702), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1872]
theorem treeEq1871 : B1871.tree = HexagonCover.NBand.M6900_7100.SplitData.node1871 := by
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
  · exact treeEq1872

def B1870 : Block := .branch 125 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 21778071483257515986038083306341688410176] ![B1871, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1870 : B1870.tree = HexagonCover.NBand.M6900_7100.SplitData.node1870 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1871
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1869 : Block := .branch 143 ![93536104789177786765038305173920684018529480999297, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 21778071483257515986038083306341688410176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1870, (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq1869 : B1869.tree = HexagonCover.NBand.M6900_7100.SplitData.node1869 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1870
  · rfl

def B1868 : Block := .branch 166 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833161406536338260419412032] ![B1869, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1868 : B1868.tree = HexagonCover.NBand.M6900_7100.SplitData.node1868 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1869
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1867 : Block := .branch 151 ![2475880078570760549798248833, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1868, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1867 : B1867.tree = HexagonCover.NBand.M6900_7100.SplitData.node1867 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1868
  · rfl

def B1866 : Block := .branch 170 ![10384596192949733827821542456689025, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833161406536338260419412032] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1867, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 705).pointIds 705)]
theorem treeEq1866 : B1866.tree = HexagonCover.NBand.M6900_7100.SplitData.node1866 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1867
  · rfl
  · rfl

def B1805 : Block := .branch 86 ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), B1806, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1866]
theorem treeEq1805 : B1805.tree = HexagonCover.NBand.M6900_7100.SplitData.node1805 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1806
  · rfl
  · rfl
  · exact treeEq1866

theorem accepted1805 : B1805.accepted = true := by decide +kernel
theorem checked1805 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1805 (maskNeeds ![10384596192949733827821542456689025, 1033954417949739582978, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1805]
  exact B1805.sound accepted1805
#print axioms checked1805

def Tip1753_1763 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1763 ![748288838313422304504880351420982458935188826096001, 907137158627434459825666, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] HexagonCover.NBand.M6900_7100.SplitTree.Run0023.checked1763
def B1762 : Block := .branch 142 ![385, 1538, 6148, 24584, 5847433797016317632695797616834581573760113016848, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq1762 : B1762.tree = HexagonCover.NBand.M6900_7100.SplitData.node1762 := by
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
  · rfl

def B1761 : Block := .branch 162 ![385, 1538, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 21799339780226640358090810431747946709056] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1762, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 742).pointIds 742)]
theorem treeEq1761 : B1761.tree = HexagonCover.NBand.M6900_7100.SplitData.node1761 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1762
  · rfl
  · rfl

def B1760 : Block := .branch 124 ![748288838313422304507415653225311531735138114208129, 1538, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 21778072132294081704124349518783461195840] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1761]
theorem treeEq1760 : B1760.tree = HexagonCover.NBand.M6900_7100.SplitData.node1760 := by
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
  · exact treeEq1761

def B1759 : Block := .branch 79 ![748288838313422304507415652621438917738182232506753, 302674248820119872472578, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1760, Tip1753_1763, (.leaf 2 (Common.fact 223).pointIds 223), (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 653).pointIds 653)]
theorem treeEq1759 : B1759.tree = HexagonCover.NBand.M6900_7100.SplitData.node1759 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1760
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1803 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 686).pointIds 686)]
theorem treeEq1803 : B1803.tree = HexagonCover.NBand.M6900_7100.SplitData.node1803 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1802 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778072132294082006355804422440754872384] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1803, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq1802 : B1802.tree = HexagonCover.NBand.M6900_7100.SplitData.node1802 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1803
  · rfl
  · rfl

def B1758 : Block := .branch 78 ![748288838313422304507415652621438917738182232506753, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![(.leaf 0 (Common.fact 146).pointIds 146), B1759, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1802]
theorem treeEq1758 : B1758.tree = HexagonCover.NBand.M6900_7100.SplitData.node1758 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1759
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1802

def B1757 : Block := .branch 101 ![748288838313422304504880351420982458935188826096001, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1758, (.leaf 1 (Common.fact 460).pointIds 460), (.leaf 2 (Common.fact 461).pointIds 461), (.leaf 3 (Common.fact 462).pointIds 462), (.leaf 4 (Common.fact 463).pointIds 463), (.leaf 5 (Common.fact 464).pointIds 464), (.leaf 6 (Common.fact 652).pointIds 652)]
theorem treeEq1757 : B1757.tree = HexagonCover.NBand.M6900_7100.SplitData.node1757 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1758
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1756 : Block := .branch 169 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489219192437863107007534568305279369280] ![B1757, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq1756 : B1756.tree = HexagonCover.NBand.M6900_7100.SplitData.node1756 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1757
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1755 : Block := .branch 109 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 2140871539058939821587428954174242704574218256, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 193).pointIds 193), (.leaf 1 (Common.fact 194).pointIds 194), (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), B1756]
theorem treeEq1755 : B1755.tree = HexagonCover.NBand.M6900_7100.SplitData.node1755 := by
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
  · exact treeEq1756

def B1754 : Block := .branch 150 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 42535295865117307932921825928971419680, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), B1755, (.leaf 5 (Common.fact 191).pointIds 191), (.leaf 6 (Common.fact 192).pointIds 192)]
theorem treeEq1754 : B1754.tree = HexagonCover.NBand.M6900_7100.SplitData.node1754 := by
  change Tree.branch (150 : Fin 173) _ = Tree.branch (150 : Fin 173) _
  apply congrArg (Tree.branch (150 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1755
  · rfl
  · rfl

def B1753 : Block := .branch 125 ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768] ![(.leaf 0 (Common.fact 650).pointIds 650), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1754, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1753 : B1753.tree = HexagonCover.NBand.M6900_7100.SplitData.node1753 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1754
  · rfl

theorem accepted1753 : B1753.accepted = true := by decide +kernel
theorem checked1753 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1753 (maskNeeds ![10384593717070245552871351364092289, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755790154081001993238216768]) := by
  rw [← treeEq1753]
  exact B1753.sound accepted1753
#print axioms checked1753

def Tip1636_1638 : Block := .tip HexagonCover.NBand.M6900_7100.SplitData.node1638 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] HexagonCover.NBand.M6900_7100.SplitTree.Run0022.checked1638
def B1742 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468372414128216807114477103961150943789088, 385836432277136441888713244355016968746685018144832] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 736).pointIds 736), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1742 : B1742.tree = HexagonCover.NBand.M6900_7100.SplitData.node1742 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1741 : Block := .branch 125 ![841824943102600080885322463644579019321817144754561, 1538, 6148, 24584, 1496577676626844588240573268701473812127674924105744, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), B1742, (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1741 : B1741.tree = HexagonCover.NBand.M6900_7100.SplitData.node1741 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1742
  · rfl

def B1740 : Block := .branch 169 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 233843116468329878832351689806544182135221972762656, 385836432277136441889030311747578936769593556336704] ![B1741, (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1740 : B1740.tree = HexagonCover.NBand.M6900_7100.SplitData.node1740 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1741
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1739 : Block := .branch 163 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 233843116468329878832351689806544182135221972762656, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), (.leaf 4 (Common.fact 734).pointIds 734), (.leaf 5 (Common.fact 262).pointIds 262), B1740]
theorem treeEq1739 : B1739.tree = HexagonCover.NBand.M6900_7100.SplitData.node1739 := by
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
  · exact treeEq1740

def B1738 : Block := .branch 165 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 187075064073740985449833775159623125506232131387424, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 358).pointIds 358), (.leaf 4 (Common.fact 733).pointIds 733), B1739, (.leaf 0 [] 0)]
theorem treeEq1738 : B1738.tree = HexagonCover.NBand.M6900_7100.SplitData.node1738 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1739
  · rfl

def B1737 : Block := .branch 167 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578395825877240853169583228388105037333491974160, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 732).pointIds 732), B1738, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq1737 : B1737.tree = HexagonCover.NBand.M6900_7100.SplitData.node1737 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1738
  · rfl

def B1736 : Block := .branch 142 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), B1737, (.leaf 5 (Common.fact 156).pointIds 156), (.leaf 6 (Common.fact 638).pointIds 638)]
theorem treeEq1736 : B1736.tree = HexagonCover.NBand.M6900_7100.SplitData.node1736 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1737
  · rfl
  · rfl

def B1735 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400833085848672612346095992896] ![B1736, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1735 : B1735.tree = HexagonCover.NBand.M6900_7100.SplitData.node1735 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1736
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1734 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1735, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1734 : B1734.tree = HexagonCover.NBand.M6900_7100.SplitData.node1734 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1735
  · rfl

def B1733 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400833085848672612346095992896] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1734, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq1733 : B1733.tree = HexagonCover.NBand.M6900_7100.SplitData.node1733 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1734
  · rfl
  · rfl

def B1637 : Block := .branch 86 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), Tip1636_1638, (.leaf 4 (Common.fact 343).pointIds 343), (.leaf 5 (Common.fact 344).pointIds 344), B1733]
theorem treeEq1637 : B1637.tree = HexagonCover.NBand.M6900_7100.SplitData.node1637 := by
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
  · exact treeEq1733

def B1750 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 216).pointIds 216), (.leaf 1 (Common.fact 217).pointIds 217), (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 604).pointIds 604), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq1750 : B1750.tree = HexagonCover.NBand.M6900_7100.SplitData.node1750 := by
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

def B1749 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 1122433257491911512663687080882554756898504945696832] ![(.leaf 0 (Common.fact 258).pointIds 258), (.leaf 1 (Common.fact 259).pointIds 259), (.leaf 2 (Common.fact 260).pointIds 260), (.leaf 3 (Common.fact 261).pointIds 261), B1750, (.leaf 5 (Common.fact 262).pointIds 262), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq1749 : B1749.tree = HexagonCover.NBand.M6900_7100.SplitData.node1749 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1750
  · rfl
  · rfl

def B1748 : Block := .branch 169 ![93536104789220322060900946601775035083908653777281, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400446531817850834667483693120] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 470).pointIds 470), (.leaf 3 (Common.fact 471).pointIds 471), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 473).pointIds 473), B1749]
theorem treeEq1748 : B1748.tree = HexagonCover.NBand.M6900_7100.SplitData.node1748 := by
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
  · exact treeEq1749

def B1747 : Block := .branch 125 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2865645758011185073687339798035314453518876704, 374144419178489218543400756016827672179736208474176] ![B1748, (.leaf 1 (Common.fact 182).pointIds 182), (.leaf 2 (Common.fact 183).pointIds 183), (.leaf 3 (Common.fact 184).pointIds 184), (.leaf 4 (Common.fact 185).pointIds 185), (.leaf 5 (Common.fact 482).pointIds 482), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq1747 : B1747.tree = HexagonCover.NBand.M6900_7100.SplitData.node1747 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1748
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1746 : Block := .branch 143 ![93536104789177786765035829293842113257979682750849, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 659).pointIds 659), B1747, (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq1746 : B1746.tree = HexagonCover.NBand.M6900_7100.SplitData.node1746 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1747
  · rfl

def B1745 : Block := .branch 166 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 2854495385411919762116571938898990272765886496, 374144419178489218543400756016827672179736208474176] ![B1746, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 269).pointIds 269), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1745 : B1745.tree = HexagonCover.NBand.M6900_7100.SplitData.node1745 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1746
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1744 : Block := .branch 151 ![385, 936749822004692482, 18482772870728521732, 38685626227668133590622216, 1496578390250690941220513797844458536875243115479056, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 696).pointIds 696), B1745, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1744 : B1744.tree = HexagonCover.NBand.M6900_7100.SplitData.node1744 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1745
  · rfl

def B1743 : Block := .branch 170 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400756016827672179736208474176] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1744, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 738).pointIds 738)]
theorem treeEq1743 : B1743.tree = HexagonCover.NBand.M6900_7100.SplitData.node1743 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1744
  · rfl
  · rfl

def B1636 : Block := .branch 78 ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632] ![(.leaf 0 (Common.fact 146).pointIds 146), B1637, (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), (.leaf 4 (Common.fact 150).pointIds 150), (.leaf 5 (Common.fact 151).pointIds 151), B1743]
theorem treeEq1636 : B1636.tree = HexagonCover.NBand.M6900_7100.SplitData.node1636 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq1637
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1743

theorem accepted1636 : B1636.accepted = true := by decide +kernel
theorem checked1636 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1636 (maskNeeds ![10384593717069655257060992658440577, 443658607591033931266, 2416559502452970231812, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 374144419178489218543400755714596217276078914797632]) := by
  rw [← treeEq1636]
  exact B1636.sound accepted1636
#print axioms checked1636

def B1920 : Block := .branch 124 ![94266855607843243416434530245027883298303978242433, 1538, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 582).pointIds 582), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), (.leaf 6 (Common.fact 499).pointIds 499)]
theorem treeEq1920 : B1920.tree = HexagonCover.NBand.M6900_7100.SplitData.node1920 := by
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
  · rfl

def B1919 : Block := .branch 159 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![B1920, (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), (.leaf 6 (Common.fact 581).pointIds 581)]
theorem treeEq1919 : B1919.tree = HexagonCover.NBand.M6900_7100.SplitData.node1919 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1920
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1918 : Block := .branch 160 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 24584, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 299).pointIds 299), (.leaf 1 (Common.fact 578).pointIds 578), B1919, (.leaf 3 (Common.fact 301).pointIds 301), (.leaf 4 (Common.fact 302).pointIds 302), (.leaf 5 (Common.fact 303).pointIds 303), (.leaf 6 (Common.fact 579).pointIds 579)]
theorem treeEq1918 : B1918.tree = HexagonCover.NBand.M6900_7100.SplitData.node1918 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1919
  · rfl
  · rfl
  · rfl
  · rfl

def B1917 : Block := .branch 161 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 98320, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 345).pointIds 345), (.leaf 1 (Common.fact 346).pointIds 346), B1918, (.leaf 3 (Common.fact 759).pointIds 759), (.leaf 4 (Common.fact 347).pointIds 347), (.leaf 5 (Common.fact 348).pointIds 348), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq1917 : B1917.tree = HexagonCover.NBand.M6900_7100.SplitData.node1917 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1918
  · rfl
  · rfl
  · rfl
  · rfl

def B1916 : Block := .branch 137 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 5847433797016317632695797616834581573760113016848, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 270).pointIds 270), (.leaf 1 (Common.fact 271).pointIds 271), (.leaf 2 (Common.fact 272).pointIds 272), B1917, (.leaf 4 (Common.fact 721).pointIds 721), (.leaf 5 (Common.fact 274).pointIds 274), (.leaf 0 [] 0)]
theorem treeEq1916 : B1916.tree = HexagonCover.NBand.M6900_7100.SplitData.node1916 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1917
  · rfl
  · rfl
  · rfl

def B1915 : Block := .branch 162 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 393248, 374144430328861818132913967490825023033041512562752] ![(.leaf 0 (Common.fact 350).pointIds 350), (.leaf 1 (Common.fact 351).pointIds 351), (.leaf 2 (Common.fact 352).pointIds 352), (.leaf 3 (Common.fact 758).pointIds 758), B1916, (.leaf 5 (Common.fact 353).pointIds 353), (.leaf 6 (Common.fact 727).pointIds 727)]
theorem treeEq1915 : B1915.tree = HexagonCover.NBand.M6900_7100.SplitData.node1915 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1916
  · rfl
  · rfl

def B1914 : Block := .branch 143 ![93536104789177791957332687828669741788476011970945, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867602396722965886708860759572544] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 577).pointIds 577), (.leaf 5 (Common.fact 498).pointIds 498), B1915]
theorem treeEq1914 : B1914.tree = HexagonCover.NBand.M6900_7100.SplitData.node1914 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1915

def B1913 : Block := .branch 166 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 2854495427947215627233879871820816201736912928, 374144419178489218867919309373022944059234935373888] ![B1914, (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 201).pointIds 201), (.leaf 3 (Common.fact 202).pointIds 202), (.leaf 4 (Common.fact 203).pointIds 203), (.leaf 5 (Common.fact 576).pointIds 576), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq1913 : B1913.tree = HexagonCover.NBand.M6900_7100.SplitData.node1913 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1912 : Block := .branch 151 ![5192296858534827628530496329220481, 619574482552498551548544514, 6148, 38690348594151003235835912, 1427247693370573878950743905901398666523017232, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 264).pointIds 264), (.leaf 1 (Common.fact 265).pointIds 265), (.leaf 2 (Common.fact 266).pointIds 266), (.leaf 3 (Common.fact 267).pointIds 267), (.leaf 4 (Common.fact 575).pointIds 575), B1913, (.leaf 6 (Common.fact 466).pointIds 466)]
theorem treeEq1912 : B1912.tree = HexagonCover.NBand.M6900_7100.SplitData.node1912 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1913
  · rfl

def B1924 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1924 : B1924.tree = HexagonCover.NBand.M6900_7100.SplitData.node1924 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1923 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1924, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1923 : B1923.tree = HexagonCover.NBand.M6900_7100.SplitData.node1923 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1924
  · rfl
  · rfl

def B1922 : Block := .branch 124 ![15576891813544522170971763886784897, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 584).pointIds 584), (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1923]
theorem treeEq1922 : B1922.tree = HexagonCover.NBand.M6900_7100.SplitData.node1922 := by
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
  · exact treeEq1923

def B1928 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 594).pointIds 594)]
theorem treeEq1928 : B1928.tree = HexagonCover.NBand.M6900_7100.SplitData.node1928 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1927 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374875169997155334616183577938833753339062845440064] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1928, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 593).pointIds 593)]
theorem treeEq1927 : B1927.tree = HexagonCover.NBand.M6900_7100.SplitData.node1927 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1928
  · rfl
  · rfl

def B1926 : Block := .branch 159 ![748288838313443577345109768609776548378649640829313, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![(.leaf 0 (Common.fact 592).pointIds 592), (.leaf 1 (Common.fact 580).pointIds 580), (.leaf 2 (Common.fact 230).pointIds 230), (.leaf 3 (Common.fact 231).pointIds 231), (.leaf 4 (Common.fact 232).pointIds 232), (.leaf 5 (Common.fact 233).pointIds 233), B1927]
theorem treeEq1926 : B1926.tree = HexagonCover.NBand.M6900_7100.SplitData.node1926 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1927

def B1930 : Block := .branch 143 ![385, 1538, 6148, 24584, 1496579103874537294200454326987443261622811306852368, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), (.leaf 3 (Common.fact 480).pointIds 480), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 498).pointIds 498), (.leaf 6 (Common.fact 591).pointIds 591)]
theorem treeEq1930 : B1930.tree = HexagonCover.NBand.M6900_7100.SplitData.node1930 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1929 : Block := .branch 170 ![10384593717069655257060992658440577, 442793916462578796034, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178511150805014294176442072742199364681792] ![(.leaf 0 (Common.fact 724).pointIds 724), (.leaf 1 (Common.fact 656).pointIds 656), (.leaf 2 (Common.fact 760).pointIds 760), (.leaf 3 (Common.fact 761).pointIds 761), B1930, (.leaf 5 (Common.fact 660).pointIds 660), (.leaf 6 (Common.fact 589).pointIds 589)]
theorem treeEq1929 : B1929.tree = HexagonCover.NBand.M6900_7100.SplitData.node1929 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1930
  · rfl
  · rfl

def B1925 : Block := .branch 124 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1926, (.leaf 1 (Common.fact 241).pointIds 241), (.leaf 2 (Common.fact 242).pointIds 242), (.leaf 3 (Common.fact 243).pointIds 243), (.leaf 4 (Common.fact 244).pointIds 244), (.leaf 5 (Common.fact 245).pointIds 245), B1929]
theorem treeEq1925 : B1925.tree = HexagonCover.NBand.M6900_7100.SplitData.node1925 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1926
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1929

def B1921 : Block := .branch 90 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489883157081735522475611829234879168576] ![B1922, B1925, (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 583).pointIds 583)]
theorem treeEq1921 : B1921.tree = HexagonCover.NBand.M6900_7100.SplitData.node1921 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1922
  · exact treeEq1925
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B1911 : Block := .branch 119 ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888] ![(.leaf 0 (Common.fact 158).pointIds 158), (.leaf 1 (Common.fact 159).pointIds 159), (.leaf 2 (Common.fact 160).pointIds 160), (.leaf 3 (Common.fact 161).pointIds 161), B1912, (.leaf 5 (Common.fact 163).pointIds 163), B1921]
theorem treeEq1911 : B1911.tree = HexagonCover.NBand.M6900_7100.SplitData.node1911 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1912
  · rfl
  · exact treeEq1921

theorem accepted1911 : B1911.accepted = true := by decide +kernel
theorem checked1911 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6900_7100.SplitData.node1911 (maskNeeds ![748288838313422309697177209955810087465685155316097, 619574925346413914615711234, 2398076729582241716228, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 374144419178489218867919309373022944059234935373888]) := by
  rw [← treeEq1911]
  exact B1911.sound accepted1911
#print axioms checked1911

end HexagonCover.NBand.M6900_7100.SplitTree.Run0024
