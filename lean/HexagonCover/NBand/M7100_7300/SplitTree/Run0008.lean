import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0685 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M7100_7300.SplitData.node0685 := by
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

def B0684 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0685]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M7100_7300.SplitData.node0684 := by
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
  · exact treeEq0685

def B0683 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0684, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M7100_7300.SplitData.node0683 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0684
  · rfl
  · rfl

def B0682 : Block := .branch 160 ![385, 906694508827259468514818, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 885).pointIds 885), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0683]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M7100_7300.SplitData.node0682 := by
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
  · exact treeEq0683

def B0681 : Block := .branch 79 ![21267647932558653966460912964485513601, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 884).pointIds 884), B0682, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M7100_7300.SplitData.node0681 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0682
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0680 : Block := .branch 124 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0681, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M7100_7300.SplitData.node0680 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0681
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0679 : Block := .branch 163 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0680]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M7100_7300.SplitData.node0679 := by
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
  · exact treeEq0680

def B0678 : Block := .branch 165 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0679, (.leaf 0 [] 0)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M7100_7300.SplitData.node0678 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl

def B0677 : Block := .branch 167 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0678, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M7100_7300.SplitData.node0677 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0678
  · rfl

def B0676 : Block := .branch 142 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0677, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M7100_7300.SplitData.node0676 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0677
  · rfl
  · rfl

def B0675 : Block := .branch 144 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0676, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M7100_7300.SplitData.node0675 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0676
  · rfl

def B0674 : Block := .branch 170 ![385, 302231599019944881161730, 18446884811197913092, 116056878683004400771817480, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 516).pointIds 516), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0675]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M7100_7300.SplitData.node0674 := by
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
  · exact treeEq0675

def B0689 : Block := .branch 161 ![385, 1538, 18446884811197913092, 1496577676626844588240573307387100039795808514629640, 98320, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), (.leaf 3 (Common.fact 667).pointIds 667), (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 668).pointIds 668)]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M7100_7300.SplitData.node0689 := by
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

def B0688 : Block := .branch 170 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 5986310706529156424445550435973870557418592698630208] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), B0689, (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M7100_7300.SplitData.node0688 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0689
  · rfl
  · rfl
  · rfl

def B0687 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0688]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M7100_7300.SplitData.node0687 := by
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
  · exact treeEq0688

def B0686 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257361167975308907893002600512] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0687, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M7100_7300.SplitData.node0686 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0687
  · rfl
  · rfl

def B0673 : Block := .branch 86 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 326).pointIds 326), (.leaf 1 (Common.fact 327).pointIds 327), (.leaf 2 (Common.fact 328).pointIds 328), B0674, (.leaf 4 (Common.fact 329).pointIds 329), (.leaf 5 (Common.fact 330).pointIds 330), B0686]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M7100_7300.SplitData.node0673 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0674
  · rfl
  · rfl
  · exact treeEq0686

theorem accepted0673 : B0673.accepted = true := by decide +kernel
theorem checked0673 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0673 (maskNeeds ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0673]
  exact B0673.sound accepted0673
#print axioms checked0673

def B0727 : Block := .branch 79 ![21267650467859855013215526316597576065, 730750818665451459101842416358141510927477900802, 6148, 24584, 98320, 393248, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 888).pointIds 888), (.leaf 1 (Common.fact 717).pointIds 717), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M7100_7300.SplitData.node0727 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0726 : Block := .branch 159 ![21267650467859855013215526316597576065, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 887).pointIds 887), B0727, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M7100_7300.SplitData.node0726 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0727
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0725 : Block := .branch 124 ![2535301201046754613352112062849, 1099511629314, 6148, 24584, 98320, 393248, 5986310706545489978057755095439408125619895990222912] ![B0726, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 713).pointIds 713)]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M7100_7300.SplitData.node0725 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0726
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0724 : Block := .branch 128 ![2535301201046754613352112062849, 1099511629314, 6148, 24584, 185542200051774784537577176028434367729757159440, 393248, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 261).pointIds 261), (.leaf 1 (Common.fact 262).pointIds 262), (.leaf 2 (Common.fact 263).pointIds 263), B0725, (.leaf 4 (Common.fact 711).pointIds 711), (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M7100_7300.SplitData.node0724 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0725
  · rfl
  · rfl
  · rfl

def B0723 : Block := .branch 138 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 116).pointIds 116), (.leaf 1 (Common.fact 117).pointIds 117), (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), B0724, (.leaf 5 (Common.fact 120).pointIds 120), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M7100_7300.SplitData.node0723 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0724
  · rfl
  · rfl

def B0722 : Block := .branch 139 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 110).pointIds 110), (.leaf 1 (Common.fact 111).pointIds 111), (.leaf 2 (Common.fact 112).pointIds 112), (.leaf 3 (Common.fact 113).pointIds 113), B0723, (.leaf 5 (Common.fact 114).pointIds 114), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M7100_7300.SplitData.node0722 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0721 : Block := .branch 140 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 104).pointIds 104), (.leaf 1 (Common.fact 105).pointIds 105), (.leaf 2 (Common.fact 106).pointIds 106), (.leaf 3 (Common.fact 107).pointIds 107), B0722, (.leaf 5 (Common.fact 108).pointIds 108), (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M7100_7300.SplitData.node0721 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0722
  · rfl
  · rfl

def B0720 : Block := .branch 141 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 98).pointIds 98), (.leaf 1 (Common.fact 99).pointIds 99), (.leaf 2 (Common.fact 100).pointIds 100), (.leaf 3 (Common.fact 101).pointIds 101), B0721, (.leaf 5 (Common.fact 102).pointIds 102), (.leaf 6 (Common.fact 842).pointIds 842)]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M7100_7300.SplitData.node0720 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0721
  · rfl
  · rfl

def B0719 : Block := .branch 142 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0720, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M7100_7300.SplitData.node0719 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0720
  · rfl
  · rfl

def B0718 : Block := .branch 165 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 840).pointIds 840), B0719, (.leaf 0 [] 0)]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M7100_7300.SplitData.node0718 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0719
  · rfl

def B0717 : Block := .branch 167 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185553350424374049849147943887570691910510149648, 393248, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 839).pointIds 839), B0718, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M7100_7300.SplitData.node0717 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0718
  · rfl

def B0716 : Block := .branch 143 ![2535301201046754613352112062849, 1099511629314, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 748288838313422294120286634350736906063837462396960, 7482888383172334566298328364140881937747570914230336] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), (.leaf 2 (Common.fact 429).pointIds 429), (.leaf 3 (Common.fact 430).pointIds 430), B0717, (.leaf 5 (Common.fact 837).pointIds 837), (.leaf 6 (Common.fact 838).pointIds 838)]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M7100_7300.SplitData.node0716 := by
  change Tree.branch (143 : Fin 173) _ = Tree.branch (143 : Fin 173) _
  apply congrArg (Tree.branch (143 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0717
  · rfl
  · rfl

def B0715 : Block := .branch 170 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 8769009823985417509222147681923925786069185880072, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0716]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M7100_7300.SplitData.node0715 := by
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
  · exact treeEq0716

def B0714 : Block := .branch 161 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), B0715, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M7100_7300.SplitData.node0714 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0715
  · rfl
  · rfl
  · rfl

def B0713 : Block := .branch 75 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 5846006549323611672814778016491359746757320794120, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0714, (.leaf 3 (Common.fact 707).pointIds 707), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 710).pointIds 710)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M7100_7300.SplitData.node0713 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0714
  · rfl
  · rfl
  · rfl
  · rfl

def B0712 : Block := .branch 162 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 5986310706545489978057755095439408125619895990222912] ![(.leaf 0 (Common.fact 336).pointIds 336), (.leaf 1 (Common.fact 337).pointIds 337), (.leaf 2 (Common.fact 338).pointIds 338), B0713, (.leaf 4 (Common.fact 703).pointIds 703), (.leaf 5 (Common.fact 339).pointIds 339), (.leaf 6 (Common.fact 704).pointIds 704)]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M7100_7300.SplitData.node0712 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0713
  · rfl
  · rfl
  · rfl

def B0711 : Block := .branch 172 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 186255823898127764478106319013159115297948532752, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 701).pointIds 701), (.leaf 5 (Common.fact 702).pointIds 702), B0712]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M7100_7300.SplitData.node0711 := by
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
  · exact treeEq0712

def B0710 : Block := .branch 151 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 38111625095462020633512877109196294193216] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), B0711, (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 697).pointIds 697)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M7100_7300.SplitData.node0710 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0711
  · rfl
  · rfl

def B0709 : Block := .branch 132 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 695).pointIds 695), (.leaf 5 (Common.fact 219).pointIds 219), B0710]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M7100_7300.SplitData.node0709 := by
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
  · exact treeEq0710

def B0708 : Block := .branch 78 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![(.leaf 0 (Common.fact 140).pointIds 140), B0709, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), (.leaf 6 (Common.fact 694).pointIds 694)]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M7100_7300.SplitData.node0708 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0709
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0708 : B0708.accepted = true := by decide +kernel
theorem checked0708 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0708 (maskNeeds ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920]) := by
  rw [← treeEq0708]
  exact B0708.sound accepted0708
#print axioms checked0708

def Tip0700_0708 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0708 ![2535301201046754613352112062849, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] checked0708
def B0707 : Block := .branch 101 ![590295810358705652097, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 32667107224727005218098883390288002809920] ![Tip0700_0708, (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 411).pointIds 411), (.leaf 5 (Common.fact 412).pointIds 412), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M7100_7300.SplitData.node0707 := by
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
  · rfl

def B0706 : Block := .branch 133 ![590295810358705652097, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 183401328512715844715989747074260125025183039504, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), (.leaf 4 (Common.fact 691).pointIds 691), (.leaf 5 (Common.fact 212).pointIds 212), B0707]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M7100_7300.SplitData.node0706 := by
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
  · exact treeEq0707

def B0705 : Block := .branch 157 ![590295810358705652097, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 748288838313422294120286634350736906063837462396960, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), B0706, (.leaf 5 (Common.fact 484).pointIds 484), (.leaf 0 [] 0)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M7100_7300.SplitData.node0705 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0706
  · rfl
  · rfl

def B0704 : Block := .branch 169 ![10384593717070245552871351364092289, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 873).pointIds 873), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), B0705, (.leaf 6 (Common.fact 690).pointIds 690)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M7100_7300.SplitData.node0704 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0705
  · rfl

def B0735 : Block := .branch 124 ![730750818665461843695559486013398570820624712065, 1538, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 855).pointIds 855), (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 856).pointIds 856)]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M7100_7300.SplitData.node0735 := by
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

def B0734 : Block := .branch 159 ![10384593717069655257060992658440577, 737869764047893693954, 6148, 24584, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![B0735, (.leaf 1 (Common.fact 890).pointIds 890), (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 854).pointIds 854)]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M7100_7300.SplitData.node0734 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0735
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0733 : Block := .branch 75 ![10384593717069655257060992658440577, 737869764047893693954, 6148, 2923003274661805836407369665432566039311865110536, 98320, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 705).pointIds 705), (.leaf 1 (Common.fact 706).pointIds 706), B0734, (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 709).pointIds 709), (.leaf 6 (Common.fact 852).pointIds 852)]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M7100_7300.SplitData.node0733 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0734
  · rfl
  · rfl
  · rfl
  · rfl

def B0732 : Block := .branch 170 ![10384593717069655257060992658440577, 738013879235969549826, 18446884811197913092, 2923003274661805836407369665432566039311865110536, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 850).pointIds 850), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0733]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M7100_7300.SplitData.node0732 := by
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
  · exact treeEq0733

def B0731 : Block := .branch 161 ![10384593717069655257060992658440577, 738013879235969549826, 18446884811197913092, 24584, 713623846352979940529142984724747568191471632, 393248, 5987772208166487327363753734025882427482827048616000] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 871).pointIds 871), B0732, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M7100_7300.SplitData.node0731 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0732
  · rfl
  · rfl
  · rfl

def B0730 : Block := .branch 172 ![10384593717069655257060992658440577, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0731]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M7100_7300.SplitData.node0730 := by
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
  · exact treeEq0731

def B0729 : Block := .branch 171 ![10384593717069655257060992658440577, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1461501659108974401460659219987178972127352586304] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0730, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M7100_7300.SplitData.node0729 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0730
  · rfl
  · rfl

def B0728 : Block := .branch 160 ![10384593717069655257060992658440577, 738013879235969549826, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 889).pointIds 889), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0729]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M7100_7300.SplitData.node0728 := by
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
  · exact treeEq0729

def B0703 : Block := .branch 69 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0704, B0728, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M7100_7300.SplitData.node0703 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0704
  · exact treeEq0728
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0737 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), (.leaf 3 (Common.fact 307).pointIds 307), (.leaf 4 (Common.fact 749).pointIds 749), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq0737 : B0737.tree = HexagonCover.NBand.M7100_7300.SplitData.node0737 := by
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

def B0736 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483256974387566043857650772869184] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0737, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M7100_7300.SplitData.node0736 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0737
  · rfl
  · rfl

def B0702 : Block := .branch 68 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![(.leaf 0 (Common.fact 680).pointIds 680), B0703, (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 682).pointIds 682), (.leaf 4 (Common.fact 683).pointIds 683), (.leaf 5 (Common.fact 684).pointIds 684), B0736]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M7100_7300.SplitData.node0702 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0703
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0736

def B0701 : Block := .branch 91 ![10384593717069655257060992658440577, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0702, (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), (.leaf 4 (Common.fact 320).pointIds 320), (.leaf 5 (Common.fact 321).pointIds 321), (.leaf 6 (Common.fact 679).pointIds 679)]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M7100_7300.SplitData.node0701 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0702
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0700 : Block := .branch 113 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] ![B0701, (.leaf 1 (Common.fact 239).pointIds 239), (.leaf 2 (Common.fact 240).pointIds 240), (.leaf 3 (Common.fact 241).pointIds 241), (.leaf 4 (Common.fact 242).pointIds 242), (.leaf 5 (Common.fact 243).pointIds 243), (.leaf 6 (Common.fact 678).pointIds 678)]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M7100_7300.SplitData.node0700 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0701
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0700 : B0700.accepted = true := by decide +kernel
theorem checked0700 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0700 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328]) := by
  rw [← treeEq0700]
  exact B0700.sound accepted0700
#print axioms checked0700

def Tip0670_0673 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0673 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0673
def Tip0670_0700 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0700 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] checked0700
def B0695 : Block := .branch 160 ![385, 302821750715115510957570, 18446884811197913092, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 886).pointIds 886), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M7100_7300.SplitData.node0695 := by
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
  · rfl

def B0694 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231454904756805305858, 18446884811197913092, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B0695, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M7100_7300.SplitData.node0694 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0695
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0693 : Block := .branch 169 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B0694, (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 873).pointIds 873), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M7100_7300.SplitData.node0693 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0694
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0692 : Block := .branch 151 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B0693, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0692 : B0692.tree = HexagonCover.NBand.M7100_7300.SplitData.node0692 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0693
  · rfl

def B0691 : Block := .branch 172 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0692]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M7100_7300.SplitData.node0691 := by
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
  · exact treeEq0692

def B0690 : Block := .branch 171 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0691, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M7100_7300.SplitData.node0690 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0691
  · rfl
  · rfl

def B0672 : Block := .branch 80 ![385, 302231599019944881161730, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0670_0673, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0690]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M7100_7300.SplitData.node0672 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690

def B0699 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M7100_7300.SplitData.node0699 := by
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

def B0698 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0699, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M7100_7300.SplitData.node0698 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0699
  · rfl
  · rfl

def B0697 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0698]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M7100_7300.SplitData.node0697 := by
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
  · exact treeEq0698

def B0696 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0697, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M7100_7300.SplitData.node0696 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0697
  · rfl
  · rfl

def B0671 : Block := .branch 78 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B0672, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0696]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M7100_7300.SplitData.node0671 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0672
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0696

def B0670 : Block := .branch 76 ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B0671, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip0670_0700]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M7100_7300.SplitData.node0670 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0671
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0670 : B0670.accepted = true := by decide +kernel
theorem checked0670 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0670 (maskNeeds ![385, 147718068877263898114, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0670]
  exact B0670.sound accepted0670
#print axioms checked0670

end HexagonCover.NBand.M7100_7300.SplitTree.Run0008
