import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0010
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0011
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0810_0813 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0813 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0010.checked0813
def Tip0810_0841 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0841 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] HexagonCover.NBand.M7100_7300.SplitTree.Run0010.checked0841
def B0836 : Block := .branch 160 ![385, 302821822912347525613058, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 910).pointIds 910), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M7100_7300.SplitData.node0836 := by
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

def B0835 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231527101988819961346, 18446745173221185540, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B0836, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M7100_7300.SplitData.node0835 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0836
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0834 : Block := .branch 169 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B0835, (.leaf 1 (Common.fact 908).pointIds 908), (.leaf 2 (Common.fact 909).pointIds 909), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M7100_7300.SplitData.node0834 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0835
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0833 : Block := .branch 151 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B0834, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0833 : B0833.tree = HexagonCover.NBand.M7100_7300.SplitData.node0833 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0834
  · rfl

def B0832 : Block := .branch 172 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0833]
theorem treeEq0832 : B0832.tree = HexagonCover.NBand.M7100_7300.SplitData.node0832 := by
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
  · exact treeEq0833

def B0831 : Block := .branch 171 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0832, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0831 : B0831.tree = HexagonCover.NBand.M7100_7300.SplitData.node0831 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0832
  · rfl
  · rfl

def B0812 : Block := .branch 80 ![385, 302231671217176895817218, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0810_0813, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0831]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M7100_7300.SplitData.node0812 := by
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
  · exact treeEq0831

def B0840 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M7100_7300.SplitData.node0840 := by
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

def B0839 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0840, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M7100_7300.SplitData.node0839 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0840
  · rfl
  · rfl

def B0838 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0839]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M7100_7300.SplitData.node0838 := by
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
  · exact treeEq0839

def B0837 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0838, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M7100_7300.SplitData.node0837 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0838
  · rfl
  · rfl

def B0811 : Block := .branch 78 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B0812, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0837]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M7100_7300.SplitData.node0811 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0812
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0837

def B0810 : Block := .branch 76 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B0811, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip0810_0841]
theorem treeEq0810 : B0810.tree = HexagonCover.NBand.M7100_7300.SplitData.node0810 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0811
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0810 : B0810.accepted = true := by decide +kernel
theorem checked0810 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0810 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0810]
  exact B0810.sound accepted0810
#print axioms checked0810

def Tip0809_0810 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0810 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0810
def B0893 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0893 : B0893.tree = HexagonCover.NBand.M7100_7300.SplitData.node0893 := by
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

def B0892 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0893]
theorem treeEq0892 : B0892.tree = HexagonCover.NBand.M7100_7300.SplitData.node0892 := by
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
  · exact treeEq0893

def B0891 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0892, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0891 : B0891.tree = HexagonCover.NBand.M7100_7300.SplitData.node0891 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0892
  · rfl
  · rfl

def B0890 : Block := .branch 160 ![385, 604463126120834189493762, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0891]
theorem treeEq0890 : B0890.tree = HexagonCover.NBand.M7100_7300.SplitData.node0890 := by
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
  · exact treeEq0891

def B0889 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0890, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0889 : B0889.tree = HexagonCover.NBand.M7100_7300.SplitData.node0889 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0890
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0888 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0889, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0888 : B0888.tree = HexagonCover.NBand.M7100_7300.SplitData.node0888 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0889
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0887 : Block := .branch 168 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0888, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0887 : B0887.tree = HexagonCover.NBand.M7100_7300.SplitData.node0887 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0888
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0886 : Block := .branch 163 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0887]
theorem treeEq0886 : B0886.tree = HexagonCover.NBand.M7100_7300.SplitData.node0886 := by
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
  · exact treeEq0887

def B0885 : Block := .branch 165 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0886, (.leaf 0 [] 0)]
theorem treeEq0885 : B0885.tree = HexagonCover.NBand.M7100_7300.SplitData.node0885 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0886
  · rfl

def B0884 : Block := .branch 167 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0885, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0884 : B0884.tree = HexagonCover.NBand.M7100_7300.SplitData.node0884 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0885
  · rfl

def B0883 : Block := .branch 142 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0884, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0883 : B0883.tree = HexagonCover.NBand.M7100_7300.SplitData.node0883 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0884
  · rfl
  · rfl

def B0882 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0883, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0882 : B0882.tree = HexagonCover.NBand.M7100_7300.SplitData.node0882 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0883
  · rfl

def B0881 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0882]
theorem treeEq0881 : B0881.tree = HexagonCover.NBand.M7100_7300.SplitData.node0881 := by
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
  · exact treeEq0882

def B0809 : Block := .branch 74 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0809_0810, B0881, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq0809 : B0809.tree = HexagonCover.NBand.M7100_7300.SplitData.node0809 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0881
  · rfl
  · rfl
  · rfl

theorem accepted0809 : B0809.accepted = true := by decide +kernel
theorem checked0809 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0809 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0809]
  exact B0809.sound accepted0809
#print axioms checked0809

def Tip0808_0809 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0809 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0809
def B0906 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0906 : B0906.tree = HexagonCover.NBand.M7100_7300.SplitData.node0906 := by
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

def B0905 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0906]
theorem treeEq0905 : B0905.tree = HexagonCover.NBand.M7100_7300.SplitData.node0905 := by
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
  · exact treeEq0906

def B0904 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0905, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0904 : B0904.tree = HexagonCover.NBand.M7100_7300.SplitData.node0904 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0905
  · rfl
  · rfl

def B0903 : Block := .branch 160 ![385, 604463126120834189493762, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0904]
theorem treeEq0903 : B0903.tree = HexagonCover.NBand.M7100_7300.SplitData.node0903 := by
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
  · exact treeEq0904

def B0902 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0903, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0902 : B0902.tree = HexagonCover.NBand.M7100_7300.SplitData.node0902 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0903
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0901 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0902, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0901 : B0901.tree = HexagonCover.NBand.M7100_7300.SplitData.node0901 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0902
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0900 : Block := .branch 168 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0901, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0900 : B0900.tree = HexagonCover.NBand.M7100_7300.SplitData.node0900 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0901
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0899 : Block := .branch 163 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0900]
theorem treeEq0899 : B0899.tree = HexagonCover.NBand.M7100_7300.SplitData.node0899 := by
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
  · exact treeEq0900

def B0898 : Block := .branch 165 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0899, (.leaf 0 [] 0)]
theorem treeEq0898 : B0898.tree = HexagonCover.NBand.M7100_7300.SplitData.node0898 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0899
  · rfl

def B0897 : Block := .branch 167 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0898, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0897 : B0897.tree = HexagonCover.NBand.M7100_7300.SplitData.node0897 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0898
  · rfl

def B0896 : Block := .branch 142 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0897, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0896 : B0896.tree = HexagonCover.NBand.M7100_7300.SplitData.node0896 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0897
  · rfl
  · rfl

def B0895 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0896, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0895 : B0895.tree = HexagonCover.NBand.M7100_7300.SplitData.node0895 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0896
  · rfl

def B0894 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0895]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M7100_7300.SplitData.node0894 := by
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
  · exact treeEq0895

def B0808 : Block := .branch 73 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0808_0809, B0894, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0808 : B0808.tree = HexagonCover.NBand.M7100_7300.SplitData.node0808 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0894
  · rfl
  · rfl
  · rfl

theorem accepted0808 : B0808.accepted = true := by decide +kernel
theorem checked0808 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0808 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0808]
  exact B0808.sound accepted0808
#print axioms checked0808

def Tip0807_0808 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0808 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0808
def B0919 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M7100_7300.SplitData.node0919 := by
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

def B0918 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0919]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M7100_7300.SplitData.node0918 := by
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
  · exact treeEq0919

def B0917 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0918, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M7100_7300.SplitData.node0917 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0918
  · rfl
  · rfl

def B0916 : Block := .branch 160 ![385, 604463126120834189493762, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0917]
theorem treeEq0916 : B0916.tree = HexagonCover.NBand.M7100_7300.SplitData.node0916 := by
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
  · exact treeEq0917

def B0915 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0916, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0915 : B0915.tree = HexagonCover.NBand.M7100_7300.SplitData.node0915 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0916
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0914 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0915, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0914 : B0914.tree = HexagonCover.NBand.M7100_7300.SplitData.node0914 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0915
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0913 : Block := .branch 168 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0914, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0913 : B0913.tree = HexagonCover.NBand.M7100_7300.SplitData.node0913 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0912 : Block := .branch 163 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0913]
theorem treeEq0912 : B0912.tree = HexagonCover.NBand.M7100_7300.SplitData.node0912 := by
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
  · exact treeEq0913

def B0911 : Block := .branch 165 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0912, (.leaf 0 [] 0)]
theorem treeEq0911 : B0911.tree = HexagonCover.NBand.M7100_7300.SplitData.node0911 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0912
  · rfl

def B0910 : Block := .branch 167 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0911, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0910 : B0910.tree = HexagonCover.NBand.M7100_7300.SplitData.node0910 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0911
  · rfl

def B0909 : Block := .branch 142 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0910, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0909 : B0909.tree = HexagonCover.NBand.M7100_7300.SplitData.node0909 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0910
  · rfl
  · rfl

def B0908 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0909, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0908 : B0908.tree = HexagonCover.NBand.M7100_7300.SplitData.node0908 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0909
  · rfl

def B0907 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0908]
theorem treeEq0907 : B0907.tree = HexagonCover.NBand.M7100_7300.SplitData.node0907 := by
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
  · exact treeEq0908

def B0807 : Block := .branch 72 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0807_0808, B0907, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0807 : B0807.tree = HexagonCover.NBand.M7100_7300.SplitData.node0807 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0907
  · rfl
  · rfl
  · rfl

theorem accepted0807 : B0807.accepted = true := by decide +kernel
theorem checked0807 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0807 (maskNeeds ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0807]
  exact B0807.sound accepted0807
#print axioms checked0807

def Tip0804_0807 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0807 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0807
def B0932 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0932 : B0932.tree = HexagonCover.NBand.M7100_7300.SplitData.node0932 := by
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

def B0931 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0932]
theorem treeEq0931 : B0931.tree = HexagonCover.NBand.M7100_7300.SplitData.node0931 := by
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
  · exact treeEq0932

def B0930 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), B0931, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0930 : B0930.tree = HexagonCover.NBand.M7100_7300.SplitData.node0930 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0931
  · rfl
  · rfl

def B0929 : Block := .branch 160 ![385, 604463126120834189493762, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 914).pointIds 914), (.leaf 2 (Common.fact 894).pointIds 894), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0930]
theorem treeEq0929 : B0929.tree = HexagonCover.NBand.M7100_7300.SplitData.node0929 := by
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
  · exact treeEq0930

def B0928 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0929, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0928 : B0928.tree = HexagonCover.NBand.M7100_7300.SplitData.node0928 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0929
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0927 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0928, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0927 : B0927.tree = HexagonCover.NBand.M7100_7300.SplitData.node0927 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0928
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0926 : Block := .branch 168 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0927, (.leaf 1 (Common.fact 902).pointIds 902), (.leaf 2 (Common.fact 903).pointIds 903), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0926 : B0926.tree = HexagonCover.NBand.M7100_7300.SplitData.node0926 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0927
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0925 : Block := .branch 163 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0926]
theorem treeEq0925 : B0925.tree = HexagonCover.NBand.M7100_7300.SplitData.node0925 := by
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
  · exact treeEq0926

def B0924 : Block := .branch 165 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0925, (.leaf 0 [] 0)]
theorem treeEq0924 : B0924.tree = HexagonCover.NBand.M7100_7300.SplitData.node0924 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0925
  · rfl

def B0923 : Block := .branch 167 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0924, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0923 : B0923.tree = HexagonCover.NBand.M7100_7300.SplitData.node0923 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0924
  · rfl

def B0922 : Block := .branch 142 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0923, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0922 : B0922.tree = HexagonCover.NBand.M7100_7300.SplitData.node0922 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0923
  · rfl
  · rfl

def B0921 : Block := .branch 144 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0922, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0921 : B0921.tree = HexagonCover.NBand.M7100_7300.SplitData.node0921 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0922
  · rfl

def B0920 : Block := .branch 170 ![385, 216313519602140674, 18446745173221185540, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 904).pointIds 904), (.leaf 2 (Common.fact 905).pointIds 905), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0921]
theorem treeEq0920 : B0920.tree = HexagonCover.NBand.M7100_7300.SplitData.node0920 := by
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
  · exact treeEq0921

def B0806 : Block := .branch 71 ![385, 147790266109278553602, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0804_0807, B0920, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0806 : B0806.tree = HexagonCover.NBand.M7100_7300.SplitData.node0806 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0920
  · rfl
  · rfl
  · rfl

def B0934 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq0934 : B0934.tree = HexagonCover.NBand.M7100_7300.SplitData.node0934 := by
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

def B0933 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B0934, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0933 : B0933.tree = HexagonCover.NBand.M7100_7300.SplitData.node0933 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0934
  · rfl
  · rfl

def B0805 : Block := .branch 67 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B0806, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0933]
theorem treeEq0805 : B0805.tree = HexagonCover.NBand.M7100_7300.SplitData.node0805 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0806
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0933

def B0936 : Block := .branch 171 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 895).pointIds 895), (.leaf 2 (Common.fact 896).pointIds 896), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0936 : B0936.tree = HexagonCover.NBand.M7100_7300.SplitData.node0936 := by
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

def B0935 : Block := .branch 172 ![385, 144115188075857410, 18446745173221185540, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 898).pointIds 898), (.leaf 2 (Common.fact 899).pointIds 899), (.leaf 3 (Common.fact 663).pointIds 663), B0936, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0935 : B0935.tree = HexagonCover.NBand.M7100_7300.SplitData.node0935 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0936
  · rfl
  · rfl

def B0804 : Block := .branch 65 ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0805, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0935]
theorem treeEq0804 : B0804.tree = HexagonCover.NBand.M7100_7300.SplitData.node0804 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0805
  · rfl
  · rfl
  · rfl
  · exact treeEq0935

theorem accepted0804 : B0804.accepted = true := by decide +kernel
theorem checked0804 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0804 (maskNeeds ![385, 216313519602140674, 18446745173221185540, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0804]
  exact B0804.sound accepted0804
#print axioms checked0804

end HexagonCover.NBand.M7100_7300.SplitTree.Run0011
