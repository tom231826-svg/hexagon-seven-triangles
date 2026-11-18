import HexagonCover.NBand.M7100_7300.SplitData
import HexagonCover.NBand.M7100_7300.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7100_7300.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M7100_7300

abbrev Block := Chunk (n := 173) (Certificate := Fin 933) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0380_0383 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0383 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] HexagonCover.NBand.M7100_7300.SplitTree.Run0004.checked0383
def Tip0380_0411 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0411 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483256974387270895952471420043328] HexagonCover.NBand.M7100_7300.SplitTree.Run0004.checked0411
def B0406 : Block := .branch 160 ![385, 302821750855852999312898, 18518801667747485700, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 830).pointIds 830), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0406 : B0406.tree = HexagonCover.NBand.M7100_7300.SplitData.node0406 := by
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

def B0405 : Block := .branch 69 ![748288838313422294120286634350736906063837462004097, 302231455045494293661186, 18518801667747485700, 24584, 98320, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 828).pointIds 828), B0406, (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 424).pointIds 424), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0405 : B0405.tree = HexagonCover.NBand.M7100_7300.SplitData.node0405 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0406
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0404 : Block := .branch 169 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 2854495385411919762116571938898990272765886496, 21778071483257130263143762513720633720896] ![B0405, (.leaf 1 (Common.fact 825).pointIds 825), (.leaf 2 (Common.fact 826).pointIds 826), (.leaf 3 (Common.fact 689).pointIds 689), (.leaf 4 (Common.fact 571).pointIds 571), (.leaf 5 (Common.fact 696).pointIds 696), (.leaf 6 (Common.fact 827).pointIds 827)]
theorem treeEq0404 : B0404.tree = HexagonCover.NBand.M7100_7300.SplitData.node0404 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0405
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0403 : Block := .branch 151 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 250).pointIds 250), (.leaf 1 (Common.fact 251).pointIds 251), (.leaf 2 (Common.fact 252).pointIds 252), (.leaf 3 (Common.fact 253).pointIds 253), (.leaf 4 (Common.fact 823).pointIds 823), B0404, (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0403 : B0403.tree = HexagonCover.NBand.M7100_7300.SplitData.node0403 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0404
  · rfl

def B0402 : Block := .branch 172 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 2993156066877535529461087066545932349002918039486480, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0403]
theorem treeEq0402 : B0402.tree = HexagonCover.NBand.M7100_7300.SplitData.node0402 := by
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
  · exact treeEq0403

def B0401 : Block := .branch 171 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257130263143762513720633720896] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0402, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0401 : B0401.tree = HexagonCover.NBand.M7100_7300.SplitData.node0401 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0402
  · rfl
  · rfl

def B0382 : Block := .branch 80 ![385, 302231599160682369517058, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![Tip0380_0383, (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 405).pointIds 405), (.leaf 4 (Common.fact 406).pointIds 406), (.leaf 5 (Common.fact 407).pointIds 407), B0401]
theorem treeEq0382 : B0382.tree = HexagonCover.NBand.M7100_7300.SplitData.node0382 := by
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
  · exact treeEq0401

def B0410 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 214).pointIds 214), (.leaf 1 (Common.fact 215).pointIds 215), (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 675).pointIds 675), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 834).pointIds 834)]
theorem treeEq0410 : B0410.tree = HexagonCover.NBand.M7100_7300.SplitData.node0410 := by
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

def B0409 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 5986310706529156424445550204162344646313448448720960] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), B0410, (.leaf 5 (Common.fact 248).pointIds 248), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0409 : B0409.tree = HexagonCover.NBand.M7100_7300.SplitData.node0409 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0410
  · rfl
  · rfl

def B0408 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155353253689176481146537402947624255349848113168, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 702).pointIds 702), B0409]
theorem treeEq0408 : B0408.tree = HexagonCover.NBand.M7100_7300.SplitData.node0408 := by
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
  · exact treeEq0409

def B0407 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0408, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 832).pointIds 832)]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M7100_7300.SplitData.node0407 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0408
  · rfl
  · rfl

def B0381 : Block := .branch 78 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 140).pointIds 140), B0382, (.leaf 2 (Common.fact 142).pointIds 142), (.leaf 3 (Common.fact 143).pointIds 143), (.leaf 4 (Common.fact 144).pointIds 144), (.leaf 5 (Common.fact 145).pointIds 145), B0407]
theorem treeEq0381 : B0381.tree = HexagonCover.NBand.M7100_7300.SplitData.node0381 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0382
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0407

def B0380 : Block := .branch 76 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), B0381, (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 401).pointIds 401), (.leaf 5 (Common.fact 402).pointIds 402), Tip0380_0411]
theorem treeEq0380 : B0380.tree = HexagonCover.NBand.M7100_7300.SplitData.node0380 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0381
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0380 : B0380.accepted = true := by decide +kernel
theorem checked0380 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0380 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0380]
  exact B0380.sound accepted0380
#print axioms checked0380

def Tip0379_0380 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0380 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0380
def B0463 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M7100_7300.SplitData.node0463 := by
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

def B0462 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0463]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M7100_7300.SplitData.node0462 := by
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
  · exact treeEq0463

def B0461 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0462, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M7100_7300.SplitData.node0461 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0462
  · rfl
  · rfl

def B0460 : Block := .branch 160 ![385, 604610628016929339606530, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0461]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M7100_7300.SplitData.node0460 := by
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
  · exact treeEq0461

def B0459 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0460, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M7100_7300.SplitData.node0459 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0460
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0458 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0459, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M7100_7300.SplitData.node0458 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0459
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0457 : Block := .branch 168 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0458, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M7100_7300.SplitData.node0457 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0458
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0456 : Block := .branch 163 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0457]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M7100_7300.SplitData.node0456 := by
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
  · exact treeEq0457

def B0455 : Block := .branch 165 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0456, (.leaf 0 [] 0)]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M7100_7300.SplitData.node0455 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0456
  · rfl

def B0454 : Block := .branch 167 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0455, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M7100_7300.SplitData.node0454 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0455
  · rfl

def B0453 : Block := .branch 142 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0454, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M7100_7300.SplitData.node0453 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0454
  · rfl
  · rfl

def B0452 : Block := .branch 144 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0453, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M7100_7300.SplitData.node0452 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0453
  · rfl

def B0451 : Block := .branch 170 ![385, 147718209614752253442, 18518801667747485700, 38704515693599612171477000, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 753).pointIds 753), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0452]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M7100_7300.SplitData.node0451 := by
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
  · exact treeEq0452

def B0379 : Block := .branch 74 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), Tip0379_0380, B0451, (.leaf 4 (Common.fact 395).pointIds 395), (.leaf 5 (Common.fact 396).pointIds 396), (.leaf 6 (Common.fact 397).pointIds 397)]
theorem treeEq0379 : B0379.tree = HexagonCover.NBand.M7100_7300.SplitData.node0379 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0451
  · rfl
  · rfl
  · rfl

theorem accepted0379 : B0379.accepted = true := by decide +kernel
theorem checked0379 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0379 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0379]
  exact B0379.sound accepted0379
#print axioms checked0379

def Tip0378_0379 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0379 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0379
def B0476 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M7100_7300.SplitData.node0476 := by
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

def B0475 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0476]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M7100_7300.SplitData.node0475 := by
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
  · exact treeEq0476

def B0474 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0475, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M7100_7300.SplitData.node0474 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0475
  · rfl
  · rfl

def B0473 : Block := .branch 160 ![385, 604610628016929339606530, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0474]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M7100_7300.SplitData.node0473 := by
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
  · exact treeEq0474

def B0472 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0473, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M7100_7300.SplitData.node0472 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0473
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0471 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0472, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M7100_7300.SplitData.node0471 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0472
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0470 : Block := .branch 168 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0471, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M7100_7300.SplitData.node0470 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0471
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0469 : Block := .branch 163 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0470]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M7100_7300.SplitData.node0469 := by
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
  · exact treeEq0470

def B0468 : Block := .branch 165 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0469, (.leaf 0 [] 0)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M7100_7300.SplitData.node0468 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0469
  · rfl

def B0467 : Block := .branch 167 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0468, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M7100_7300.SplitData.node0467 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0468
  · rfl

def B0466 : Block := .branch 142 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0467, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M7100_7300.SplitData.node0466 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0467
  · rfl
  · rfl

def B0465 : Block := .branch 144 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0466, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M7100_7300.SplitData.node0465 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0466
  · rfl

def B0464 : Block := .branch 170 ![385, 147718209614752253442, 18518801667747485700, 38695070960633872881049608, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 772).pointIds 772), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0465]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M7100_7300.SplitData.node0464 := by
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
  · exact treeEq0465

def B0378 : Block := .branch 73 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), Tip0378_0379, B0464, (.leaf 4 (Common.fact 390).pointIds 390), (.leaf 5 (Common.fact 391).pointIds 391), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0378 : B0378.tree = HexagonCover.NBand.M7100_7300.SplitData.node0378 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0464
  · rfl
  · rfl
  · rfl

theorem accepted0378 : B0378.accepted = true := by decide +kernel
theorem checked0378 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0378 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0378]
  exact B0378.sound accepted0378
#print axioms checked0378

def Tip0377_0378 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0378 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0378
def B0489 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M7100_7300.SplitData.node0489 := by
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

def B0488 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0489]
theorem treeEq0488 : B0488.tree = HexagonCover.NBand.M7100_7300.SplitData.node0488 := by
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
  · exact treeEq0489

def B0487 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0488, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0487 : B0487.tree = HexagonCover.NBand.M7100_7300.SplitData.node0487 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0488
  · rfl
  · rfl

def B0486 : Block := .branch 160 ![385, 604610628016929339606530, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0487]
theorem treeEq0486 : B0486.tree = HexagonCover.NBand.M7100_7300.SplitData.node0486 := by
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
  · exact treeEq0487

def B0485 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0486, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0485 : B0485.tree = HexagonCover.NBand.M7100_7300.SplitData.node0485 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0486
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0484 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0485, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0484 : B0484.tree = HexagonCover.NBand.M7100_7300.SplitData.node0484 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0485
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0483 : Block := .branch 168 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0484, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0483 : B0483.tree = HexagonCover.NBand.M7100_7300.SplitData.node0483 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0484
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0482 : Block := .branch 163 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0483]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M7100_7300.SplitData.node0482 := by
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
  · exact treeEq0483

def B0481 : Block := .branch 165 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0482, (.leaf 0 [] 0)]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M7100_7300.SplitData.node0481 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0482
  · rfl

def B0480 : Block := .branch 167 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0481, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M7100_7300.SplitData.node0480 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0481
  · rfl

def B0479 : Block := .branch 142 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0480, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0479 : B0479.tree = HexagonCover.NBand.M7100_7300.SplitData.node0479 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0480
  · rfl
  · rfl

def B0478 : Block := .branch 144 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0479, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M7100_7300.SplitData.node0478 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0479
  · rfl

def B0477 : Block := .branch 170 ![385, 147718209614752253442, 18518801667747485700, 38690348594151003235835912, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0478]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M7100_7300.SplitData.node0477 := by
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
  · exact treeEq0478

def B0377 : Block := .branch 72 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), Tip0377_0378, B0477, (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0377 : B0377.tree = HexagonCover.NBand.M7100_7300.SplitData.node0377 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0477
  · rfl
  · rfl
  · rfl

theorem accepted0377 : B0377.accepted = true := by decide +kernel
theorem checked0377 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0377 (maskNeeds ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0377]
  exact B0377.sound accepted0377
#print axioms checked0377

def Tip0374_0377 : Block := .tip HexagonCover.NBand.M7100_7300.SplitData.node0377 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] checked0377
def B0502 : Block := .branch 129 ![385, 1538, 6148, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 7496041897891979138949639723405976493363995296137280] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), (.leaf 3 (Common.fact 300).pointIds 300), (.leaf 4 (Common.fact 565).pointIds 565), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 820).pointIds 820)]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M7100_7300.SplitData.node0502 := by
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

def B0501 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 2993155358828875476113802322786877192417440224608272, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), (.leaf 4 (Common.fact 769).pointIds 769), (.leaf 5 (Common.fact 702).pointIds 702), B0502]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M7100_7300.SplitData.node0501 := by
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
  · exact treeEq0502

def B0500 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1509731191384600785987346648600081244853295600107584] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), B0501, (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 817).pointIds 817)]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M7100_7300.SplitData.node0500 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl
  · rfl

def B0499 : Block := .branch 160 ![385, 604610628016929339606530, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069142963767364961833639667564608] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 857).pointIds 857), (.leaf 2 (Common.fact 814).pointIds 814), (.leaf 3 (Common.fact 287).pointIds 287), (.leaf 4 (Common.fact 288).pointIds 288), (.leaf 5 (Common.fact 289).pointIds 289), B0500]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M7100_7300.SplitData.node0499 := by
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
  · exact treeEq0500

def B0498 : Block := .branch 79 ![374144419156732414708075875829334913944883216515457, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![(.leaf 0 (Common.fact 758).pointIds 758), B0499, (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), (.leaf 5 (Common.fact 224).pointIds 224), (.leaf 6 (Common.fact 759).pointIds 759)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M7100_7300.SplitData.node0498 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0499
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0497 : Block := .branch 124 ![374144419156711147060143317175368453031918731002241, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 5575186299632655785383929568162090376593424, 393248, 1508269689747269883069143273252374783178708392345664] ![B0498, (.leaf 1 (Common.fact 188).pointIds 188), (.leaf 2 (Common.fact 189).pointIds 189), (.leaf 3 (Common.fact 190).pointIds 190), (.leaf 4 (Common.fact 191).pointIds 191), (.leaf 5 (Common.fact 192).pointIds 192), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M7100_7300.SplitData.node0497 := by
  change Tree.branch (124 : Fin 173) _ = Tree.branch (124 : Fin 173) _
  apply congrArg (Tree.branch (124 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0498
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0496 : Block := .branch 168 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1508269689747269883069143273252374783178708392345664] ![B0497, (.leaf 1 (Common.fact 807).pointIds 807), (.leaf 2 (Common.fact 808).pointIds 808), (.leaf 3 (Common.fact 372).pointIds 372), (.leaf 4 (Common.fact 373).pointIds 373), (.leaf 5 (Common.fact 374).pointIds 374), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M7100_7300.SplitData.node0496 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0497
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0495 : Block := .branch 163 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 244).pointIds 244), (.leaf 1 (Common.fact 245).pointIds 245), (.leaf 2 (Common.fact 246).pointIds 246), (.leaf 3 (Common.fact 247).pointIds 247), (.leaf 4 (Common.fact 539).pointIds 539), (.leaf 5 (Common.fact 248).pointIds 248), B0496]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M7100_7300.SplitData.node0495 := by
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
  · exact treeEq0496

def B0494 : Block := .branch 165 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 341).pointIds 341), (.leaf 1 (Common.fact 342).pointIds 342), (.leaf 2 (Common.fact 343).pointIds 343), (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 538).pointIds 538), B0495, (.leaf 0 [] 0)]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M7100_7300.SplitData.node0494 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0495
  · rfl

def B0493 : Block := .branch 167 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 719199032652612596314526914292909658567966736, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 532).pointIds 532), (.leaf 1 (Common.fact 533).pointIds 533), (.leaf 2 (Common.fact 534).pointIds 534), (.leaf 3 (Common.fact 535).pointIds 535), (.leaf 4 (Common.fact 536).pointIds 536), B0494, (.leaf 6 (Common.fact 537).pointIds 537)]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M7100_7300.SplitData.node0493 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0494
  · rfl

def B0492 : Block := .branch 142 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 146).pointIds 146), (.leaf 1 (Common.fact 147).pointIds 147), (.leaf 2 (Common.fact 148).pointIds 148), (.leaf 3 (Common.fact 149).pointIds 149), B0493, (.leaf 5 (Common.fact 150).pointIds 150), (.leaf 6 (Common.fact 755).pointIds 755)]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M7100_7300.SplitData.node0492 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0493
  · rfl
  · rfl

def B0491 : Block := .branch 144 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 1496577676648622659723513794590644519021460932001856] ![(.leaf 0 (Common.fact 134).pointIds 134), (.leaf 1 (Common.fact 135).pointIds 135), (.leaf 2 (Common.fact 136).pointIds 136), (.leaf 3 (Common.fact 137).pointIds 137), (.leaf 4 (Common.fact 138).pointIds 138), B0492, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M7100_7300.SplitData.node0491 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0492
  · rfl

def B0490 : Block := .branch 170 ![385, 147718209614752253442, 18518801667747485700, 38687987410909568413229064, 713623846352979940529142984724747568191471632, 393248, 21778071482940525889170706893786007994432] ![(.leaf 0 (Common.fact 751).pointIds 751), (.leaf 1 (Common.fact 811).pointIds 811), (.leaf 2 (Common.fact 812).pointIds 812), (.leaf 3 (Common.fact 784).pointIds 784), (.leaf 4 (Common.fact 528).pointIds 528), (.leaf 5 (Common.fact 529).pointIds 529), B0491]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M7100_7300.SplitData.node0490 := by
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
  · exact treeEq0491

def B0376 : Block := .branch 71 ![385, 147718209614752253442, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), Tip0374_0377, B0490, (.leaf 4 (Common.fact 324).pointIds 324), (.leaf 5 (Common.fact 325).pointIds 325), (.leaf 0 [] 0)]
theorem treeEq0376 : B0376.tree = HexagonCover.NBand.M7100_7300.SplitData.node0376 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0490
  · rfl
  · rfl
  · rfl

def B0504 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 152).pointIds 152), (.leaf 1 (Common.fact 153).pointIds 153), (.leaf 2 (Common.fact 154).pointIds 154), (.leaf 3 (Common.fact 155).pointIds 155), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 157).pointIds 157), (.leaf 6 (Common.fact 792).pointIds 792)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M7100_7300.SplitData.node0504 := by
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

def B0503 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), B0504, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M7100_7300.SplitData.node0503 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0504
  · rfl
  · rfl

def B0375 : Block := .branch 67 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 378).pointIds 378), B0376, (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0503]
theorem treeEq0375 : B0375.tree = HexagonCover.NBand.M7100_7300.SplitData.node0375 := by
  change Tree.branch (67 : Fin 173) _ = Tree.branch (67 : Fin 173) _
  apply congrArg (Tree.branch (67 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0376
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0503

def B0506 : Block := .branch 171 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 762).pointIds 762), (.leaf 1 (Common.fact 815).pointIds 815), (.leaf 2 (Common.fact 816).pointIds 816), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 743).pointIds 743), (.leaf 5 (Common.fact 740).pointIds 740), (.leaf 6 (Common.fact 860).pointIds 860)]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M7100_7300.SplitData.node0506 := by
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

def B0505 : Block := .branch 172 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 766).pointIds 766), (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 663).pointIds 663), B0506, (.leaf 5 (Common.fact 702).pointIds 702), (.leaf 6 (Common.fact 859).pointIds 859)]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M7100_7300.SplitData.node0505 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0506
  · rfl
  · rfl

def B0374 : Block := .branch 65 ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 122).pointIds 122), (.leaf 1 (Common.fact 123).pointIds 123), B0375, (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B0505]
theorem treeEq0374 : B0374.tree = HexagonCover.NBand.M7100_7300.SplitData.node0374 := by
  change Tree.branch (65 : Fin 173) _ = Tree.branch (65 : Fin 173) _
  apply congrArg (Tree.branch (65 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0375
  · rfl
  · rfl
  · rfl
  · exact treeEq0505

theorem accepted0374 : B0374.accepted = true := by decide +kernel
theorem checked0374 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7100_7300.SplitData.node0374 (maskNeeds ![385, 144257025075840514, 18518801667747485700, 38685626227668133590622216, 713623846352979940529142984724747568191471632, 393248, 21778071483257438539227764244160183795776]) := by
  rw [← treeEq0374]
  exact B0374.sound accepted0374
#print axioms checked0374

end HexagonCover.NBand.M7100_7300.SplitTree.Run0005
