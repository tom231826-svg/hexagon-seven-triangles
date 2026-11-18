import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0005
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0006
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B0515 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995953122419862861159358529600] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 775).pointIds 775), (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M7700_7900.SplitData.node0515 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0514 : Block := .branch 89 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 773).pointIds 773), (.leaf 1 (Common.fact 774).pointIds 774), (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0515]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M7700_7900.SplitData.node0514 := by
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
  · exact treeEq0515

def B0513 : Block := .branch 159 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 767).pointIds 767), (.leaf 1 (Common.fact 768).pointIds 768), (.leaf 2 (Common.fact 769).pointIds 769), (.leaf 3 (Common.fact 770).pointIds 770), (.leaf 4 (Common.fact 771).pointIds 771), (.leaf 5 (Common.fact 772).pointIds 772), B0514]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M7700_7900.SplitData.node0513 := by
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
  · exact treeEq0514

def B0512 : Block := .branch 124 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![B0513, (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), (.leaf 6 (Common.fact 766).pointIds 766)]
theorem treeEq0512 : B0512.tree = HexagonCover.NBand.M7700_7900.SplitData.node0512 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0513
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0511 : Block := .branch 128 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0512, (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0511 : B0511.tree = HexagonCover.NBand.M7700_7900.SplitData.node0511 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0512
  · rfl
  · rfl
  · rfl

def B0510 : Block := .branch 138 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0511, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0510 : B0510.tree = HexagonCover.NBand.M7700_7900.SplitData.node0510 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0511
  · rfl
  · rfl

def B0509 : Block := .branch 139 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0510, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0509 : B0509.tree = HexagonCover.NBand.M7700_7900.SplitData.node0509 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0510
  · rfl
  · rfl

def B0508 : Block := .branch 140 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0509, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0508 : B0508.tree = HexagonCover.NBand.M7700_7900.SplitData.node0508 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0509
  · rfl
  · rfl

def B0507 : Block := .branch 141 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0508, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0507 : B0507.tree = HexagonCover.NBand.M7700_7900.SplitData.node0507 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0508
  · rfl
  · rfl

def B0506 : Block := .branch 160 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 9295429630892709892, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 759).pointIds 759), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0507]
theorem treeEq0506 : B0506.tree = HexagonCover.NBand.M7700_7900.SplitData.node0506 := by
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
  · exact treeEq0507

def B0505 : Block := .branch 169 ![1496577676626844588243108569902520566741027036070273, 140737488356866, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![(.leaf 0 (Common.fact 757).pointIds 757), B0506, (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0505 : B0505.tree = HexagonCover.NBand.M7700_7900.SplitData.node0505 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0506
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0504 : Block := .branch 170 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![B0505, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0504 : B0504.tree = HexagonCover.NBand.M7700_7900.SplitData.node0504 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0505
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0503 : Block := .branch 162 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0504]
theorem treeEq0503 : B0503.tree = HexagonCover.NBand.M7700_7900.SplitData.node0503 := by
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
  · exact treeEq0504

def B0502 : Block := .branch 101 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0503, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0502 : B0502.tree = HexagonCover.NBand.M7700_7900.SplitData.node0502 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0503
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0501 : Block := .branch 163 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0502]
theorem treeEq0501 : B0501.tree = HexagonCover.NBand.M7700_7900.SplitData.node0501 := by
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
  · exact treeEq0502

def B0500 : Block := .branch 165 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0501, (.leaf 0 [] 0)]
theorem treeEq0500 : B0500.tree = HexagonCover.NBand.M7700_7900.SplitData.node0500 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0501
  · rfl

def B0499 : Block := .branch 167 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0500, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0499 : B0499.tree = HexagonCover.NBand.M7700_7900.SplitData.node0499 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0500
  · rfl

def B0498 : Block := .branch 143 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0499, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0498 : B0498.tree = HexagonCover.NBand.M7700_7900.SplitData.node0498 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0499
  · rfl
  · rfl

def B0497 : Block := .branch 144 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0498, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0497 : B0497.tree = HexagonCover.NBand.M7700_7900.SplitData.node0497 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0498
  · rfl

def B0496 : Block := .branch 161 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 722).pointIds 722), (.leaf 3 (Common.fact 777).pointIds 777), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0497]
theorem treeEq0496 : B0496.tree = HexagonCover.NBand.M7700_7900.SplitData.node0496 := by
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
  · exact treeEq0497

theorem accepted0496 : B0496.accepted = true := by decide +kernel
theorem checked0496 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0496 (maskNeeds ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0496]
  exact B0496.sound accepted0496
#print axioms checked0496

def B0535 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995953122419862861159358529600] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 775).pointIds 775), (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq0535 : B0535.tree = HexagonCover.NBand.M7700_7900.SplitData.node0535 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0534 : Block := .branch 89 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 773).pointIds 773), (.leaf 1 (Common.fact 774).pointIds 774), (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0535]
theorem treeEq0534 : B0534.tree = HexagonCover.NBand.M7700_7900.SplitData.node0534 := by
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
  · exact treeEq0535

def B0533 : Block := .branch 159 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 767).pointIds 767), (.leaf 1 (Common.fact 768).pointIds 768), (.leaf 2 (Common.fact 769).pointIds 769), (.leaf 3 (Common.fact 770).pointIds 770), (.leaf 4 (Common.fact 771).pointIds 771), (.leaf 5 (Common.fact 772).pointIds 772), B0534]
theorem treeEq0533 : B0533.tree = HexagonCover.NBand.M7700_7900.SplitData.node0533 := by
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
  · exact treeEq0534

def B0532 : Block := .branch 124 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![B0533, (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), (.leaf 6 (Common.fact 766).pointIds 766)]
theorem treeEq0532 : B0532.tree = HexagonCover.NBand.M7700_7900.SplitData.node0532 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0533
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0531 : Block := .branch 128 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0532, (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0531 : B0531.tree = HexagonCover.NBand.M7700_7900.SplitData.node0531 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0532
  · rfl
  · rfl
  · rfl

def B0530 : Block := .branch 138 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0531, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0530 : B0530.tree = HexagonCover.NBand.M7700_7900.SplitData.node0530 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0531
  · rfl
  · rfl

def B0529 : Block := .branch 139 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0530, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0529 : B0529.tree = HexagonCover.NBand.M7700_7900.SplitData.node0529 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0530
  · rfl
  · rfl

def B0528 : Block := .branch 140 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0529, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0528 : B0528.tree = HexagonCover.NBand.M7700_7900.SplitData.node0528 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0529
  · rfl
  · rfl

def B0527 : Block := .branch 141 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0528, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0527 : B0527.tree = HexagonCover.NBand.M7700_7900.SplitData.node0527 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0528
  · rfl
  · rfl

def B0526 : Block := .branch 160 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 9295429630892709892, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 759).pointIds 759), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0527]
theorem treeEq0526 : B0526.tree = HexagonCover.NBand.M7700_7900.SplitData.node0526 := by
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
  · exact treeEq0527

def B0525 : Block := .branch 169 ![1496577676626844588243108569902520566741027036070273, 140737488356866, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![(.leaf 0 (Common.fact 757).pointIds 757), B0526, (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0525 : B0525.tree = HexagonCover.NBand.M7700_7900.SplitData.node0525 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0526
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0524 : Block := .branch 170 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![B0525, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0524 : B0524.tree = HexagonCover.NBand.M7700_7900.SplitData.node0524 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0525
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0523 : Block := .branch 162 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0524]
theorem treeEq0523 : B0523.tree = HexagonCover.NBand.M7700_7900.SplitData.node0523 := by
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
  · exact treeEq0524

def B0522 : Block := .branch 101 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0523, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0522 : B0522.tree = HexagonCover.NBand.M7700_7900.SplitData.node0522 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0523
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0521 : Block := .branch 163 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0522]
theorem treeEq0521 : B0521.tree = HexagonCover.NBand.M7700_7900.SplitData.node0521 := by
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
  · exact treeEq0522

def B0520 : Block := .branch 165 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0521, (.leaf 0 [] 0)]
theorem treeEq0520 : B0520.tree = HexagonCover.NBand.M7700_7900.SplitData.node0520 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0521
  · rfl

def B0519 : Block := .branch 167 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0520, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0519 : B0519.tree = HexagonCover.NBand.M7700_7900.SplitData.node0519 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0520
  · rfl

def B0518 : Block := .branch 143 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0519, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0518 : B0518.tree = HexagonCover.NBand.M7700_7900.SplitData.node0518 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0519
  · rfl
  · rfl

def B0517 : Block := .branch 144 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0518, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0517 : B0517.tree = HexagonCover.NBand.M7700_7900.SplitData.node0517 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0518
  · rfl

def B0516 : Block := .branch 161 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 722).pointIds 722), (.leaf 3 (Common.fact 779).pointIds 779), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0517]
theorem treeEq0516 : B0516.tree = HexagonCover.NBand.M7700_7900.SplitData.node0516 := by
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
  · exact treeEq0517

theorem accepted0516 : B0516.accepted = true := by decide +kernel
theorem checked0516 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0516 (maskNeeds ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0516]
  exact B0516.sound accepted0516
#print axioms checked0516

def B0555 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995953122419862861159358529600] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 775).pointIds 775), (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq0555 : B0555.tree = HexagonCover.NBand.M7700_7900.SplitData.node0555 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0554 : Block := .branch 89 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 773).pointIds 773), (.leaf 1 (Common.fact 774).pointIds 774), (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0555]
theorem treeEq0554 : B0554.tree = HexagonCover.NBand.M7700_7900.SplitData.node0554 := by
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
  · exact treeEq0555

def B0553 : Block := .branch 159 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 767).pointIds 767), (.leaf 1 (Common.fact 768).pointIds 768), (.leaf 2 (Common.fact 769).pointIds 769), (.leaf 3 (Common.fact 770).pointIds 770), (.leaf 4 (Common.fact 771).pointIds 771), (.leaf 5 (Common.fact 772).pointIds 772), B0554]
theorem treeEq0553 : B0553.tree = HexagonCover.NBand.M7700_7900.SplitData.node0553 := by
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
  · exact treeEq0554

def B0552 : Block := .branch 124 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![B0553, (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), (.leaf 6 (Common.fact 766).pointIds 766)]
theorem treeEq0552 : B0552.tree = HexagonCover.NBand.M7700_7900.SplitData.node0552 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0553
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0551 : Block := .branch 128 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0552, (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0551 : B0551.tree = HexagonCover.NBand.M7700_7900.SplitData.node0551 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0552
  · rfl
  · rfl
  · rfl

def B0550 : Block := .branch 138 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0551, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0550 : B0550.tree = HexagonCover.NBand.M7700_7900.SplitData.node0550 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0551
  · rfl
  · rfl

def B0549 : Block := .branch 139 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0550, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0549 : B0549.tree = HexagonCover.NBand.M7700_7900.SplitData.node0549 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0550
  · rfl
  · rfl

def B0548 : Block := .branch 140 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0549, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0548 : B0548.tree = HexagonCover.NBand.M7700_7900.SplitData.node0548 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0549
  · rfl
  · rfl

def B0547 : Block := .branch 141 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0548, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0547 : B0547.tree = HexagonCover.NBand.M7700_7900.SplitData.node0547 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0548
  · rfl
  · rfl

def B0546 : Block := .branch 160 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 9295429630892709892, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 759).pointIds 759), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0547]
theorem treeEq0546 : B0546.tree = HexagonCover.NBand.M7700_7900.SplitData.node0546 := by
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
  · exact treeEq0547

def B0545 : Block := .branch 169 ![1496577676626844588243108569902520566741027036070273, 140737488356866, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![(.leaf 0 (Common.fact 757).pointIds 757), B0546, (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0545 : B0545.tree = HexagonCover.NBand.M7700_7900.SplitData.node0545 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0546
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0544 : Block := .branch 170 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![B0545, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0544 : B0544.tree = HexagonCover.NBand.M7700_7900.SplitData.node0544 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0545
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0543 : Block := .branch 162 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 782).pointIds 782), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0544]
theorem treeEq0543 : B0543.tree = HexagonCover.NBand.M7700_7900.SplitData.node0543 := by
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
  · exact treeEq0544

def B0542 : Block := .branch 101 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0543, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0542 : B0542.tree = HexagonCover.NBand.M7700_7900.SplitData.node0542 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0543
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0541 : Block := .branch 163 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0542]
theorem treeEq0541 : B0541.tree = HexagonCover.NBand.M7700_7900.SplitData.node0541 := by
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
  · exact treeEq0542

def B0540 : Block := .branch 165 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0541, (.leaf 0 [] 0)]
theorem treeEq0540 : B0540.tree = HexagonCover.NBand.M7700_7900.SplitData.node0540 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0541
  · rfl

def B0539 : Block := .branch 167 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0540, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0539 : B0539.tree = HexagonCover.NBand.M7700_7900.SplitData.node0539 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0540
  · rfl

def B0538 : Block := .branch 143 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0539, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0538 : B0538.tree = HexagonCover.NBand.M7700_7900.SplitData.node0538 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0539
  · rfl
  · rfl

def B0537 : Block := .branch 144 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0538, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0537 : B0537.tree = HexagonCover.NBand.M7700_7900.SplitData.node0537 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0538
  · rfl

def B0536 : Block := .branch 161 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 722).pointIds 722), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0537]
theorem treeEq0536 : B0536.tree = HexagonCover.NBand.M7700_7900.SplitData.node0536 := by
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
  · exact treeEq0537

theorem accepted0536 : B0536.accepted = true := by decide +kernel
theorem checked0536 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0536 (maskNeeds ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0536]
  exact B0536.sound accepted0536
#print axioms checked0536

def Tip0423_0430 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0430 ![590295810358705652097, 302231599159582857889282, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0005.checked0430
def Tip0423_0476 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0476 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] HexagonCover.NBand.M7700_7900.SplitTree.Run0005.checked0476
def Tip0423_0496 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0496 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266857585224971466424999944, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] checked0496
def Tip0423_0516 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0516 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266852862858488596779786248, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] checked0516
def Tip0423_0536 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0536 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266850501675247161957179400, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] checked0536
def B0475 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 185542200051774784537577176028434367729757159440, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 746).pointIds 746), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0475 : B0475.tree = HexagonCover.NBand.M7700_7900.SplitData.node0475 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0474 : Block := .branch 151 ![385, 1538, 6148, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 42535295865117307932921825928971419680, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), B0475, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 745).pointIds 745)]
theorem treeEq0474 : B0474.tree = HexagonCover.NBand.M7700_7900.SplitData.node0474 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0475
  · rfl
  · rfl

def B0473 : Block := .branch 122 ![385, 1538, 6148, 38685626227668133590622216, 184114952359068824656518890058984872593374412816, 42535295865117307932921825928971419680, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 472).pointIds 472), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), B0474]
theorem treeEq0473 : B0473.tree = HexagonCover.NBand.M7700_7900.SplitData.node0473 := by
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
  · exact treeEq0474

def B0472 : Block := .branch 157 ![385, 1538, 6148, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 42535295865117307932921825928971419680, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0473, (.leaf 5 (Common.fact 470).pointIds 470), (.leaf 0 [] 0)]
theorem treeEq0472 : B0472.tree = HexagonCover.NBand.M7700_7900.SplitData.node0472 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0473
  · rfl
  · rfl

def B0471 : Block := .branch 125 ![1496577676626844588240573268702064107938033629659521, 1538, 6148, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 465).pointIds 465), (.leaf 2 (Common.fact 466).pointIds 466), (.leaf 3 (Common.fact 467).pointIds 467), (.leaf 4 (Common.fact 468).pointIds 468), B0472, (.leaf 6 (Common.fact 744).pointIds 744)]
theorem treeEq0471 : B0471.tree = HexagonCover.NBand.M7700_7900.SplitData.node0471 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0472
  · rfl

def B0470 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0471, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0470 : B0470.tree = HexagonCover.NBand.M7700_7900.SplitData.node0470 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0471
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0429 : Block := .branch 78 ![590295810358705652097, 144255925564212738, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), Tip0423_0430, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0470]
theorem treeEq0429 : B0429.tree = HexagonCover.NBand.M7700_7900.SplitData.node0429 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0470

def B0428 : Block := .branch 74 ![590295810358705652097, 144255925564212738, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), B0429, Tip0423_0476, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0428 : B0428.tree = HexagonCover.NBand.M7700_7900.SplitData.node0428 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0429
  · rfl
  · rfl
  · rfl
  · rfl

def B0427 : Block := .branch 73 ![590295810358705652097, 144255925564212738, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), B0428, Tip0423_0496, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0427 : B0427.tree = HexagonCover.NBand.M7700_7900.SplitData.node0427 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0428
  · rfl
  · rfl
  · rfl
  · rfl

def B0426 : Block := .branch 72 ![590295810358705652097, 144255925564212738, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), B0427, Tip0423_0516, (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0426 : B0426.tree = HexagonCover.NBand.M7700_7900.SplitData.node0426 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0427
  · rfl
  · rfl
  · rfl
  · rfl

def B0425 : Block := .branch 71 ![590295810358705652097, 144255925564212738, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0426, Tip0423_0536, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0425 : B0425.tree = HexagonCover.NBand.M7700_7900.SplitData.node0425 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0426
  · rfl
  · rfl
  · rfl
  · rfl

def B0558 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0558 : B0558.tree = HexagonCover.NBand.M7700_7900.SplitData.node0558 := by
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

def B0557 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0558, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0557 : B0557.tree = HexagonCover.NBand.M7700_7900.SplitData.node0557 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0558
  · rfl
  · rfl

def B0556 : Block := .branch 170 ![385, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054808238709450164666432] ![B0557, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq0556 : B0556.tree = HexagonCover.NBand.M7700_7900.SplitData.node0556 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0557
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0424 : Block := .branch 69 ![385, 148294669267544049154, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0425, (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 460).pointIds 460), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 462).pointIds 462), (.leaf 5 (Common.fact 463).pointIds 463), B0556]
theorem treeEq0424 : B0424.tree = HexagonCover.NBand.M7700_7900.SplitData.node0424 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0425
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0556

def B0562 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0562 : B0562.tree = HexagonCover.NBand.M7700_7900.SplitData.node0562 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0561 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0562, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0561 : B0561.tree = HexagonCover.NBand.M7700_7900.SplitData.node0561 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0562
  · rfl
  · rfl

def B0560 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0561, (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq0560 : B0560.tree = HexagonCover.NBand.M7700_7900.SplitData.node0560 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0561
  · rfl

def B0559 : Block := .branch 170 ![385, 144255925564212738, 9295429630892709892, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054365516851681135427648] ![B0560, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq0559 : B0559.tree = HexagonCover.NBand.M7700_7900.SplitData.node0559 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0560
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0423 : Block := .branch 67 ![385, 720716677867636226, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 167).pointIds 167), B0424, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), B0559]
theorem treeEq0423 : B0423.tree = HexagonCover.NBand.M7700_7900.SplitData.node0423 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0424
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0559

theorem accepted0423 : B0423.accepted = true := by decide +kernel
theorem checked0423 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0423 (maskNeeds ![385, 720716677867636226, 9331458427911673860, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0423]
  exact B0423.sound accepted0423
#print axioms checked0423

end HexagonCover.NBand.M7700_7900.SplitTree.Run0006
