import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0006
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0007
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0521_0524 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0524 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0006.checked0524
def Tip0521_0552 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0552 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] HexagonCover.NBand.M7100_7300.SplitTree.Run0006.checked0552
def B0547 : Block := .branch 160 ![385, 302821822772709548885506, 18446884811197913092, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 874).pointIds 874), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0547 : B0547.tree = HexagonCover.NBand.M7100_7300.SplitData.node0547 := by
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

def B0546 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231526962350843233794, 18446884811197913092, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B0547, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M7100_7300.SplitData.node0546 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0547
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0545 : Block := .branch 169 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B0546, (.leaf 1 (Common.fact 872).pointIds 872), (.leaf 2 (Common.fact 873).pointIds 873), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq0545 : B0545.tree = HexagonCover.NBand.M7100_7300.SplitData.node0545 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0546
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0544 : Block := .branch 151 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B0545, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0544 : B0544.tree = HexagonCover.NBand.M7100_7300.SplitData.node0544 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0545
  · rfl

def B0543 : Block := .branch 172 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0544]
theorem treeEq0543 : B0543.tree = HexagonCover.NBand.M7100_7300.SplitData.node0543 := by
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
  · exact treeEq0544

def B0542 : Block := .branch 171 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0543, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0542 : B0542.tree = HexagonCover.NBand.M7100_7300.SplitData.node0542 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0543
  · rfl
  · rfl

def B0523 : Block := .branch 80 ![385, 302231671077538919089666, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0521_0524, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0542]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M7100_7300.SplitData.node0523 := by
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
  · exact treeEq0542

def B0551 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M7100_7300.SplitData.node0551 := by
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

def B0550 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0551, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M7100_7300.SplitData.node0550 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0551
  · rfl
  · rfl

def B0549 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0550]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M7100_7300.SplitData.node0549 := by
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
  · exact treeEq0550

def B0548 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0549, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M7100_7300.SplitData.node0548 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0549
  · rfl
  · rfl

def B0522 : Block := .branch 78 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B0523, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0548]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M7100_7300.SplitData.node0522 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0523
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0548

def B0521 : Block := .branch 76 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B0522, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip0521_0552]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M7100_7300.SplitData.node0521 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0522
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0521 : B0521.accepted = true := by decide +kernel
theorem checked0521 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0521 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0521]
  exact B0521.sound accepted0521
#print axioms checked0521

def Tip0520_0521 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0521 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0521
def B0604 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0604 : B0604.tree = HexagonCover.NBand.M7100_7300.SplitData.node0604 := by
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

def B0603 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0604]
theorem treeEq0603 : B0603.tree = HexagonCover.NBand.M7100_7300.SplitData.node0603 := by
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
  · exact treeEq0604

def B0602 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0603, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0602 : B0602.tree = HexagonCover.NBand.M7100_7300.SplitData.node0602 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0603
  · rfl
  · rfl

def B0601 : Block := .branch 160 ![385, 604463125981196212766210, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0602]
theorem treeEq0601 : B0601.tree = HexagonCover.NBand.M7100_7300.SplitData.node0601 := by
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
  · exact treeEq0602

def B0600 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0601, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0600 : B0600.tree = HexagonCover.NBand.M7100_7300.SplitData.node0600 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0601
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0599 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0600, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0599 : B0599.tree = HexagonCover.NBand.M7100_7300.SplitData.node0599 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0600
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0598 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0599, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M7100_7300.SplitData.node0598 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0599
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0597 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0598]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M7100_7300.SplitData.node0597 := by
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
  · exact treeEq0598

def B0596 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0597, (.leaf 0 [] 0)]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M7100_7300.SplitData.node0596 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0597
  · rfl

def B0595 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0596, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0595 : B0595.tree = HexagonCover.NBand.M7100_7300.SplitData.node0595 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0596
  · rfl

def B0594 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0595, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0594 : B0594.tree = HexagonCover.NBand.M7100_7300.SplitData.node0594 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0595
  · rfl
  · rfl

def B0593 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0594, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0593 : B0593.tree = HexagonCover.NBand.M7100_7300.SplitData.node0593 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0594
  · rfl

def B0592 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0593]
theorem treeEq0592 : B0592.tree = HexagonCover.NBand.M7100_7300.SplitData.node0592 := by
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
  · exact treeEq0593

def B0520 : Block := .branch 74 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0520_0521, B0592, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M7100_7300.SplitData.node0520 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0592
  · rfl
  · rfl
  · rfl

theorem accepted0520 : B0520.accepted = true := by decide +kernel
theorem checked0520 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0520 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0520]
  exact B0520.sound accepted0520
#print axioms checked0520

def Tip0519_0520 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0520 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0520
def B0617 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0617 : B0617.tree = HexagonCover.NBand.M7100_7300.SplitData.node0617 := by
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

def B0616 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0617]
theorem treeEq0616 : B0616.tree = HexagonCover.NBand.M7100_7300.SplitData.node0616 := by
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
  · exact treeEq0617

def B0615 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0616, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0615 : B0615.tree = HexagonCover.NBand.M7100_7300.SplitData.node0615 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0616
  · rfl
  · rfl

def B0614 : Block := .branch 160 ![385, 604463125981196212766210, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0615]
theorem treeEq0614 : B0614.tree = HexagonCover.NBand.M7100_7300.SplitData.node0614 := by
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
  · exact treeEq0615

def B0613 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0614, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0613 : B0613.tree = HexagonCover.NBand.M7100_7300.SplitData.node0613 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0614
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0612 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0613, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0612 : B0612.tree = HexagonCover.NBand.M7100_7300.SplitData.node0612 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0613
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0611 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0612, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0611 : B0611.tree = HexagonCover.NBand.M7100_7300.SplitData.node0611 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0612
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0610 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0611]
theorem treeEq0610 : B0610.tree = HexagonCover.NBand.M7100_7300.SplitData.node0610 := by
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
  · exact treeEq0611

def B0609 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0610, (.leaf 0 [] 0)]
theorem treeEq0609 : B0609.tree = HexagonCover.NBand.M7100_7300.SplitData.node0609 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0610
  · rfl

def B0608 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0609, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0608 : B0608.tree = HexagonCover.NBand.M7100_7300.SplitData.node0608 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0609
  · rfl

def B0607 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0608, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0607 : B0607.tree = HexagonCover.NBand.M7100_7300.SplitData.node0607 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0608
  · rfl
  · rfl

def B0606 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0607, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0606 : B0606.tree = HexagonCover.NBand.M7100_7300.SplitData.node0606 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0607
  · rfl

def B0605 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0606]
theorem treeEq0605 : B0605.tree = HexagonCover.NBand.M7100_7300.SplitData.node0605 := by
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
  · exact treeEq0606

def B0519 : Block := .branch 73 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0519_0520, B0605, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0519 : B0519.tree = HexagonCover.NBand.M7100_7300.SplitData.node0519 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0605
  · rfl
  · rfl
  · rfl

theorem accepted0519 : B0519.accepted = true := by decide +kernel
theorem checked0519 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0519 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0519]
  exact B0519.sound accepted0519
#print axioms checked0519

def Tip0518_0519 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0519 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0519
def B0630 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M7100_7300.SplitData.node0630 := by
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

def B0629 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0630]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M7100_7300.SplitData.node0629 := by
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
  · exact treeEq0630

def B0628 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0629, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M7100_7300.SplitData.node0628 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0629
  · rfl
  · rfl

def B0627 : Block := .branch 160 ![385, 604463125981196212766210, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0628]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M7100_7300.SplitData.node0627 := by
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
  · exact treeEq0628

def B0626 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0627, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0626 : B0626.tree = HexagonCover.NBand.M7100_7300.SplitData.node0626 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0627
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0625 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0626, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0625 : B0625.tree = HexagonCover.NBand.M7100_7300.SplitData.node0625 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0626
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0624 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0625, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0624 : B0624.tree = HexagonCover.NBand.M7100_7300.SplitData.node0624 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0625
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0623 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0624]
theorem treeEq0623 : B0623.tree = HexagonCover.NBand.M7100_7300.SplitData.node0623 := by
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
  · exact treeEq0624

def B0622 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0623, (.leaf 0 [] 0)]
theorem treeEq0622 : B0622.tree = HexagonCover.NBand.M7100_7300.SplitData.node0622 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0623
  · rfl

def B0621 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0622, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0621 : B0621.tree = HexagonCover.NBand.M7100_7300.SplitData.node0621 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0622
  · rfl

def B0620 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0621, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0620 : B0620.tree = HexagonCover.NBand.M7100_7300.SplitData.node0620 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0621
  · rfl
  · rfl

def B0619 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0620, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0619 : B0619.tree = HexagonCover.NBand.M7100_7300.SplitData.node0619 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0620
  · rfl

def B0618 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0619]
theorem treeEq0618 : B0618.tree = HexagonCover.NBand.M7100_7300.SplitData.node0618 := by
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
  · exact treeEq0619

def B0518 : Block := .branch 72 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0518_0519, B0618, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0518 : B0518.tree = HexagonCover.NBand.M7100_7300.SplitData.node0518 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0618
  · rfl
  · rfl
  · rfl

theorem accepted0518 : B0518.accepted = true := by decide +kernel
theorem checked0518 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0518 (maskNeeds ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0518]
  exact B0518.sound accepted0518
#print axioms checked0518

def Tip0515_0518 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0518 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0518
def B0643 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M7100_7300.SplitData.node0643 := by
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

def B0642 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0643]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M7100_7300.SplitData.node0642 := by
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
  · exact treeEq0643

def B0641 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), B0642, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M7100_7300.SplitData.node0641 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0642
  · rfl
  · rfl

def B0640 : Block := .branch 160 ![385, 604463125981196212766210, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 876).pointIds 876), (.leaf 2 (Common.fact 866).pointIds 866), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0641]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M7100_7300.SplitData.node0640 := by
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
  · exact treeEq0641

def B0639 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0640, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M7100_7300.SplitData.node0639 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0640
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0638 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0639, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M7100_7300.SplitData.node0638 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0639
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0637 : Block := .branch 168 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0638, (.leaf 1 (Common.fact 862).pointIds 862), (.leaf 2 (Common.fact 863).pointIds 863), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M7100_7300.SplitData.node0637 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0638
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0636 : Block := .branch 163 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0637]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M7100_7300.SplitData.node0636 := by
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
  · exact treeEq0637

def B0635 : Block := .branch 165 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0636, (.leaf 0 [] 0)]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M7100_7300.SplitData.node0635 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0636
  · rfl

def B0634 : Block := .branch 167 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0635, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M7100_7300.SplitData.node0634 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0635
  · rfl

def B0633 : Block := .branch 142 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0634, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M7100_7300.SplitData.node0633 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0634
  · rfl
  · rfl

def B0632 : Block := .branch 144 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0633, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M7100_7300.SplitData.node0632 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0633
  · rfl

def B0631 : Block := .branch 170 ![385, 216173881625413122, 18446884811197913092, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 864).pointIds 864), (.leaf 2 (Common.fact 865).pointIds 865), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0632]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M7100_7300.SplitData.node0631 := by
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
  · exact treeEq0632

def B0517 : Block := .branch 71 ![385, 147790126471301826050, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0515_0518, B0631, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0517 : B0517.tree = HexagonCover.NBand.M7100_7300.SplitData.node0517 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0631
  · rfl
  · rfl
  · rfl

def B0645 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M7100_7300.SplitData.node0645 := by
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

def B0644 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0645, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M7100_7300.SplitData.node0644 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0645
  · rfl
  · rfl

def B0516 : Block := .branch 67 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B0517, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0644]
theorem treeEq0516 : B0516.tree = HexagonCover.NBand.M7100_7300.SplitData.node0516 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0517
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0644

def B0647 : Block := .branch 171 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 867).pointIds 867), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M7100_7300.SplitData.node0647 := by
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

def B0646 : Block := .branch 172 ![385, 144116287587485186, 18446884811197913092, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 869).pointIds 869), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 663).pointIds 663), B0647, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M7100_7300.SplitData.node0646 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0647
  · rfl
  · rfl

def B0515 : Block := .branch 65 ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0516, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0646]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M7100_7300.SplitData.node0515 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0516
  · rfl
  · rfl
  · rfl
  · exact treeEq0646

theorem accepted0515 : B0515.accepted = true := by decide +kernel
theorem checked0515 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0515 (maskNeeds ![385, 216173881625413122, 18446884811197913092, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0515]
  exact B0515.sound accepted0515
#print axioms checked0515

end HexagonCover.NBand.M7100_7300.SplitTree.Run0007
