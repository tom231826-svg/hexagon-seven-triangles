import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0008
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0009
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0669_0670 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0670 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0008.checked0670
def B0749 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0749 : B0749.tree = HexagonCover.NBand.M7100_7300.SplitData.node0749 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0748 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0749]
theorem treeEq0748 : B0748.tree = HexagonCover.NBand.M7100_7300.SplitData.node0748 := by
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
  · exact treeEq0749

def B0747 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0748, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0747 : B0747.tree = HexagonCover.NBand.M7100_7300.SplitData.node0747 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0748
  · rfl
  · rfl

def B0746 : Block := .branch 160 ![385, 604610627876191851251202, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 891).pointIds 891), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0747]
theorem treeEq0746 : B0746.tree = HexagonCover.NBand.M7100_7300.SplitData.node0746 := by
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
  · exact treeEq0747

def B0745 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B0746, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0745 : B0745.tree = HexagonCover.NBand.M7100_7300.SplitData.node0745 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0746
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0744 : Block := .branch 124 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0745, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0744 : B0744.tree = HexagonCover.NBand.M7100_7300.SplitData.node0744 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0745
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0743 : Block := .branch 163 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0744]
theorem treeEq0743 : B0743.tree = HexagonCover.NBand.M7100_7300.SplitData.node0743 := by
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
  · exact treeEq0744

def B0742 : Block := .branch 165 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0743, (.leaf 0 [] 0)]
theorem treeEq0742 : B0742.tree = HexagonCover.NBand.M7100_7300.SplitData.node0742 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0743
  · rfl

def B0741 : Block := .branch 167 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0742, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0741 : B0741.tree = HexagonCover.NBand.M7100_7300.SplitData.node0741 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0742
  · rfl

def B0740 : Block := .branch 142 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0741, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0740 : B0740.tree = HexagonCover.NBand.M7100_7300.SplitData.node0740 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0741
  · rfl
  · rfl

def B0739 : Block := .branch 144 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0740, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0739 : B0739.tree = HexagonCover.NBand.M7100_7300.SplitData.node0739 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0740
  · rfl

def B0738 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0739]
theorem treeEq0738 : B0738.tree = HexagonCover.NBand.M7100_7300.SplitData.node0738 := by
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
  · exact treeEq0739

def B0669 : Block := .branch 74 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0669_0670, B0738, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M7100_7300.SplitData.node0669 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0738
  · rfl
  · rfl
  · rfl

theorem accepted0669 : B0669.accepted = true := by decide +kernel
theorem checked0669 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0669 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0669]
  exact B0669.sound accepted0669
#print axioms checked0669

def Tip0668_0669 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0669 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0669
def B0761 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0761 : B0761.tree = HexagonCover.NBand.M7100_7300.SplitData.node0761 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0760 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0761]
theorem treeEq0760 : B0760.tree = HexagonCover.NBand.M7100_7300.SplitData.node0760 := by
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
  · exact treeEq0761

def B0759 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0760, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0759 : B0759.tree = HexagonCover.NBand.M7100_7300.SplitData.node0759 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0760
  · rfl
  · rfl

def B0758 : Block := .branch 160 ![385, 604610627876191851251202, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 891).pointIds 891), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0759]
theorem treeEq0758 : B0758.tree = HexagonCover.NBand.M7100_7300.SplitData.node0758 := by
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
  · exact treeEq0759

def B0757 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B0758, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0757 : B0757.tree = HexagonCover.NBand.M7100_7300.SplitData.node0757 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0758
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0756 : Block := .branch 124 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0757, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0756 : B0756.tree = HexagonCover.NBand.M7100_7300.SplitData.node0756 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0757
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0755 : Block := .branch 163 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0756]
theorem treeEq0755 : B0755.tree = HexagonCover.NBand.M7100_7300.SplitData.node0755 := by
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
  · exact treeEq0756

def B0754 : Block := .branch 165 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0755, (.leaf 0 [] 0)]
theorem treeEq0754 : B0754.tree = HexagonCover.NBand.M7100_7300.SplitData.node0754 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0755
  · rfl

def B0753 : Block := .branch 167 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0754, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0753 : B0753.tree = HexagonCover.NBand.M7100_7300.SplitData.node0753 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0754
  · rfl

def B0752 : Block := .branch 142 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0753, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0752 : B0752.tree = HexagonCover.NBand.M7100_7300.SplitData.node0752 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0753
  · rfl
  · rfl

def B0751 : Block := .branch 144 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0752, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0751 : B0751.tree = HexagonCover.NBand.M7100_7300.SplitData.node0751 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0752
  · rfl

def B0750 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0751]
theorem treeEq0750 : B0750.tree = HexagonCover.NBand.M7100_7300.SplitData.node0750 := by
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
  · exact treeEq0751

def B0668 : Block := .branch 73 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0668_0669, B0750, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M7100_7300.SplitData.node0668 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0750
  · rfl
  · rfl
  · rfl

theorem accepted0668 : B0668.accepted = true := by decide +kernel
theorem checked0668 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0668 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0668]
  exact B0668.sound accepted0668
#print axioms checked0668

def Tip0667_0668 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0668 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0668
def B0773 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0773 : B0773.tree = HexagonCover.NBand.M7100_7300.SplitData.node0773 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0772 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0773]
theorem treeEq0772 : B0772.tree = HexagonCover.NBand.M7100_7300.SplitData.node0772 := by
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
  · exact treeEq0773

def B0771 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0772, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0771 : B0771.tree = HexagonCover.NBand.M7100_7300.SplitData.node0771 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0772
  · rfl
  · rfl

def B0770 : Block := .branch 160 ![385, 604610627876191851251202, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 891).pointIds 891), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0771]
theorem treeEq0770 : B0770.tree = HexagonCover.NBand.M7100_7300.SplitData.node0770 := by
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
  · exact treeEq0771

def B0769 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B0770, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0769 : B0769.tree = HexagonCover.NBand.M7100_7300.SplitData.node0769 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0770
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0768 : Block := .branch 124 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0769, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0768 : B0768.tree = HexagonCover.NBand.M7100_7300.SplitData.node0768 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0769
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0767 : Block := .branch 163 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0768]
theorem treeEq0767 : B0767.tree = HexagonCover.NBand.M7100_7300.SplitData.node0767 := by
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
  · exact treeEq0768

def B0766 : Block := .branch 165 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0767, (.leaf 0 [] 0)]
theorem treeEq0766 : B0766.tree = HexagonCover.NBand.M7100_7300.SplitData.node0766 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0767
  · rfl

def B0765 : Block := .branch 167 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0766, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0765 : B0765.tree = HexagonCover.NBand.M7100_7300.SplitData.node0765 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0766
  · rfl

def B0764 : Block := .branch 142 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0765, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0764 : B0764.tree = HexagonCover.NBand.M7100_7300.SplitData.node0764 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0765
  · rfl
  · rfl

def B0763 : Block := .branch 144 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0764, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0763 : B0763.tree = HexagonCover.NBand.M7100_7300.SplitData.node0763 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0764
  · rfl

def B0762 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0763]
theorem treeEq0762 : B0762.tree = HexagonCover.NBand.M7100_7300.SplitData.node0762 := by
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
  · exact treeEq0763

def B0667 : Block := .branch 72 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0667_0668, B0762, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M7100_7300.SplitData.node0667 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0762
  · rfl
  · rfl
  · rfl

theorem accepted0667 : B0667.accepted = true := by decide +kernel
theorem checked0667 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0667 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0667]
  exact B0667.sound accepted0667
#print axioms checked0667

def Tip0664_0667 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0667 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0667
def B0785 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M7100_7300.SplitData.node0785 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0784 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0785]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M7100_7300.SplitData.node0784 := by
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
  · exact treeEq0785

def B0783 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0784, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M7100_7300.SplitData.node0783 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0784
  · rfl
  · rfl

def B0782 : Block := .branch 160 ![385, 604610627876191851251202, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 891).pointIds 891), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0783]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M7100_7300.SplitData.node0782 := by
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
  · exact treeEq0783

def B0781 : Block := .branch 79 ![21267647932558653966460912964485513601, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B0782, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M7100_7300.SplitData.node0781 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0782
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0780 : Block := .branch 124 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0781, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M7100_7300.SplitData.node0780 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0781
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0779 : Block := .branch 163 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0780]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M7100_7300.SplitData.node0779 := by
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
  · exact treeEq0780

def B0778 : Block := .branch 165 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0779, (.leaf 0 [] 0)]
theorem treeEq0778 : B0778.tree = HexagonCover.NBand.M7100_7300.SplitData.node0778 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0779
  · rfl

def B0777 : Block := .branch 167 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0778, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0777 : B0777.tree = HexagonCover.NBand.M7100_7300.SplitData.node0777 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0778
  · rfl

def B0776 : Block := .branch 142 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0777, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0776 : B0776.tree = HexagonCover.NBand.M7100_7300.SplitData.node0776 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0777
  · rfl
  · rfl

def B0775 : Block := .branch 144 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0776, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0775 : B0775.tree = HexagonCover.NBand.M7100_7300.SplitData.node0775 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0776
  · rfl

def B0774 : Block := .branch 170 ![385, 147718068877263898114, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0775]
theorem treeEq0774 : B0774.tree = HexagonCover.NBand.M7100_7300.SplitData.node0774 := by
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
  · exact treeEq0775

def B0666 : Block := .branch 71 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0664_0667, B0774, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M7100_7300.SplitData.node0666 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0774
  · rfl
  · rfl
  · rfl

def B0787 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq0787 : B0787.tree = HexagonCover.NBand.M7100_7300.SplitData.node0787 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0786 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0787, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M7100_7300.SplitData.node0786 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0787
  · rfl
  · rfl

def B0665 : Block := .branch 67 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B0666, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0786]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M7100_7300.SplitData.node0665 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0666
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0786

def B0789 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0789 : B0789.tree = HexagonCover.NBand.M7100_7300.SplitData.node0789 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0788 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0789, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0788 : B0788.tree = HexagonCover.NBand.M7100_7300.SplitData.node0788 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0789
  · rfl
  · rfl

def B0664 : Block := .branch 65 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0665, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0788]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M7100_7300.SplitData.node0664 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0665
  · rfl
  · rfl
  · rfl
  · exact treeEq0788

theorem accepted0664 : B0664.accepted = true := by decide +kernel
theorem checked0664 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0664 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0664]
  exact B0664.sound accepted0664
#print axioms checked0664

def Tip0648_0664 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0664 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0664
def B0655 : Block := .branch 90 ![288230376151712129, 374144419156711147060143317175368453033018242631170, 6148, 24584, 98320, 393248, 1461501664553492272195829302348219637655682940992] ![(.leaf 0 (Common.fact 879).pointIds 879), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M7100_7300.SplitData.node0655 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0654 : Block := .branch 160 ![288230376151712129, 374144419156711147060143317175368453033018242631170, 18446884811197913092, 24584, 98320, 393248, 27222589353992144469631936617999750398016] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 878).pointIds 878), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0655]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M7100_7300.SplitData.node0654 := by
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
  · exact treeEq0655

def B0653 : Block := .branch 168 ![288230376151712129, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 345).pointIds 345), B0654, (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M7100_7300.SplitData.node0653 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0654
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0652 : Block := .branch 132 ![288230376151712129, 1099511629314, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0653]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M7100_7300.SplitData.node0652 := by
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
  · exact treeEq0653

def B0651 : Block := .branch 133 ![288230376151712129, 1099511629314, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0652]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M7100_7300.SplitData.node0651 := by
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
  · exact treeEq0652

def B0650 : Block := .branch 157 ![288230376151712129, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0651, (.leaf 5 (Common.fact 206).pointIds 206), (.leaf 0 [] 0)]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M7100_7300.SplitData.node0650 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0651
  · rfl
  · rfl

def B0649 : Block := .branch 166 ![288230376151712129, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 196).pointIds 196), (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B0650, (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M7100_7300.SplitData.node0649 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0650
  · rfl

def B0663 : Block := .branch 90 ![576460752303423873, 374144419156711147060143317175368453033018242631170, 6148, 24584, 98320, 393248, 1461501664553492272195829302348219637655682940992] ![(.leaf 0 (Common.fact 883).pointIds 883), (.leaf 1 (Common.fact 880).pointIds 880), (.leaf 2 (Common.fact 448).pointIds 448), (.leaf 3 (Common.fact 449).pointIds 449), (.leaf 4 (Common.fact 450).pointIds 450), (.leaf 5 (Common.fact 451).pointIds 451), (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M7100_7300.SplitData.node0663 := by
  change Tree.branch (90 : Fin 173) _ = Tree.branch (90 : Fin 173) _
  apply congrArg (Tree.branch (90 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0662 : Block := .branch 160 ![576460752303423873, 374144419156711147060143317175368453033018242631170, 18446884811197913092, 24584, 98320, 393248, 27222589353992144469631936617999750398016] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 878).pointIds 878), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0663]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M7100_7300.SplitData.node0662 := by
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
  · exact treeEq0663

def B0661 : Block := .branch 168 ![576460752303423873, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 27222589353992453954641757963068475179072] ![(.leaf 0 (Common.fact 369).pointIds 369), B0662, (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 877).pointIds 877)]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M7100_7300.SplitData.node0661 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0662
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0660 : Block := .branch 132 ![576460752303423873, 1099511629314, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0661]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M7100_7300.SplitData.node0660 := by
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
  · exact treeEq0661

def B0659 : Block := .branch 133 ![576460752303423873, 1099511629314, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0660]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M7100_7300.SplitData.node0659 := by
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
  · exact treeEq0660

def B0658 : Block := .branch 157 ![576460752303423873, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 93536104789177786765035829293842113257979683143712, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0659, (.leaf 5 (Common.fact 206).pointIds 206), (.leaf 0 [] 0)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M7100_7300.SplitData.node0658 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0659
  · rfl
  · rfl

def B0657 : Block := .branch 166 ![576460752303423873, 1099511629314, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 882).pointIds 882), (.leaf 1 (Common.fact 197).pointIds 197), (.leaf 2 (Common.fact 198).pointIds 198), (.leaf 3 (Common.fact 199).pointIds 199), (.leaf 4 (Common.fact 200).pointIds 200), B0658, (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M7100_7300.SplitData.node0657 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0658
  · rfl

def B0656 : Block := .branch 59 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0657, Tip0648_0664, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), (.leaf 6 (Common.fact 368).pointIds 368)]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M7100_7300.SplitData.node0656 := by
  change Tree.branch (59 : Fin 173) _ = Tree.branch (59 : Fin 173) _
  apply congrArg (Tree.branch (59 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0657
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0648 : Block := .branch 58 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![B0649, B0656, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 168).pointIds 168)]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M7100_7300.SplitData.node0648 := by
  change Tree.branch (58 : Fin 173) _ = Tree.branch (58 : Fin 173) _
  apply congrArg (Tree.branch (58 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0649
  · exact treeEq0656
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0648 : B0648.accepted = true := by decide +kernel
theorem checked0648 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0648 (maskNeeds ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0648]
  exact B0648.sound accepted0648
#print axioms checked0648

end HexagonCover.NBand.M7100_7300.SplitTree.Run0009
