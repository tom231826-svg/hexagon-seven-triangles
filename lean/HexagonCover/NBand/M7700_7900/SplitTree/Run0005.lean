import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0004
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0005
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0038_0115 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0115 ![385, 148654816500245333506, 64617717822256060420, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0004.checked0115
def Tip0038_0040 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0040 ![576460752303423873, 216172782113785346, 9277485601127405572, 79266848140492005727134572552, 98320, 393248, 21778071483256974311713032226557096624192] HexagonCover.NBand.M7700_7900.SplitTree.Run0004.checked0040
def B0409 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0409 : B0409.tree = HexagonCover.NBand.M7700_7900.SplitData.node0409 := by
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

def B0408 : Block := .branch 143 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0409, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq0408 : B0408.tree = HexagonCover.NBand.M7700_7900.SplitData.node0408 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0409
  · rfl
  · rfl

def B0407 : Block := .branch 144 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0408, (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq0407 : B0407.tree = HexagonCover.NBand.M7700_7900.SplitData.node0407 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0408
  · rfl

def B0114 : Block := .branch 67 ![385, 1080863910568920578, 64617717822256060420, 79266848140492005727134572552, 1605653654294204866190571715630682028430688272, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 167).pointIds 167), Tip0038_0115, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), B0407]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M7700_7900.SplitData.node0114 := by
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
  · exact treeEq0407

def B0113 : Block := .branch 150 ![385, 1080863910568920578, 64617717822256060420, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), B0114, (.leaf 5 (Common.fact 110).pointIds 110), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M7700_7900.SplitData.node0113 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0114
  · rfl
  · rfl

def B0112 : Block := .branch 152 ![385, 1080863910568920578, 64617717822256060420, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), B0113, (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M7700_7900.SplitData.node0112 := by
  change Tree.branch (152 : Fin 172) _ = Tree.branch (152 : Fin 172) _
  apply congrArg (Tree.branch (152 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0113
  · rfl

def B0111 : Block := .branch 87 ![385, 1080863910568920578, 64617717822256060420, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 328).pointIds 328), (.leaf 1 (Common.fact 329).pointIds 329), (.leaf 2 (Common.fact 456).pointIds 456), (.leaf 3 (Common.fact 331).pointIds 331), (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B0112]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M7700_7900.SplitData.node0111 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0112

def B0411 : Block := .branch 124 ![748288838313422294120286634350736906063837462004097, 1538, 6148, 24584, 98320, 393248, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 668).pointIds 668), (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), (.leaf 6 (Common.fact 669).pointIds 669)]
theorem treeEq0411 : B0411.tree = HexagonCover.NBand.M7700_7900.SplitData.node0411 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0410 : Block := .branch 169 ![385, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311749925714704515727424] ![B0411, (.leaf 1 (Common.fact 482).pointIds 482), (.leaf 2 (Common.fact 483).pointIds 483), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 485).pointIds 485), (.leaf 5 (Common.fact 486).pointIds 486), (.leaf 6 (Common.fact 667).pointIds 667)]
theorem treeEq0410 : B0410.tree = HexagonCover.NBand.M7700_7900.SplitData.node0410 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0411
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0110 : Block := .branch 65 ![385, 1080863910568920578, 27724229674836957188, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 452).pointIds 452), B0111, (.leaf 3 (Common.fact 453).pointIds 453), (.leaf 4 (Common.fact 454).pointIds 454), (.leaf 5 (Common.fact 455).pointIds 455), B0410]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M7700_7900.SplitData.node0110 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0111
  · rfl
  · rfl
  · rfl
  · exact treeEq0410

def B0039 : Block := .branch 59 ![385, 504403158265497090, 27724229674836957188, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![Tip0038_0040, B0110, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M7700_7900.SplitData.node0039 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0110
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0038 : Block := .branch 64 ![385, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 215).pointIds 215), B0039, (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M7700_7900.SplitData.node0038 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0039
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0038 : B0038.accepted = true := by decide +kernel
theorem checked0038 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0038 (maskNeeds ![385, 504403158265497090, 9277485601127405572, 79266848140492005727134572552, 178405961588244985132285746181186892047941648, 393248, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0038]
  exact B0038.sound accepted0038
#print axioms checked0038

def B0464 : Block := .branch 171 ![1496577676626865855891041128556487027653991521583489, 748288838313422294120287872290776191584849849484802, 153476982750857507379204, 8769009998209989372742602289545497123000919547912, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 729).pointIds 729), (.leaf 3 (Common.fact 730).pointIds 730), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0464 : B0464.tree = HexagonCover.NBand.M7700_7900.SplitData.node0464 := by
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
  · rfl

def B0465 : Block := .branch 171 ![1496577676626865855891041128556487027653991521583489, 748288838313422294120287872290776191584849849484802, 153476982750857507379204, 8769009823985417509222108996297698117935595282440, 182699029263533993607524665196470706703068921872, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 727).pointIds 727), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 729).pointIds 729), (.leaf 3 (Common.fact 734).pointIds 734), (.leaf 4 (Common.fact 735).pointIds 735), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 733).pointIds 733)]
theorem treeEq0465 : B0465.tree = HexagonCover.NBand.M7700_7900.SplitData.node0465 := by
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
  · rfl

def B0463 : Block := .branch 137 ![1496577676626865855891041128556487027653991521583489, 748288838313422294120287872290776191584849849484802, 153476982750857507379204, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), B0464, B0465, (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 0 [] 0)]
theorem treeEq0463 : B0463.tree = HexagonCover.NBand.M7700_7900.SplitData.node0463 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0464
  · exact treeEq0465
  · rfl
  · rfl

def B0466 : Block := .branch 171 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872290776191584849849484802, 153476982750857507379204, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659810806782918955787790021386338687254592] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 729).pointIds 729), (.leaf 3 (Common.fact 734).pointIds 734), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 737).pointIds 737)]
theorem treeEq0466 : B0466.tree = HexagonCover.NBand.M7700_7900.SplitData.node0466 := by
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
  · rfl

def B0462 : Block := .branch 124 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872290776191584849849484802, 153476982750857507379204, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![B0463, (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), B0466]
theorem treeEq0462 : B0462.tree = HexagonCover.NBand.M7700_7900.SplitData.node0462 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0463
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0466

def B0467 : Block := .branch 171 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872290776191584849849484802, 77992906001238022166532, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22458641409078952017030990745905795694656] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 738).pointIds 738), (.leaf 3 (Common.fact 734).pointIds 734), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 739).pointIds 739)]
theorem treeEq0467 : B0467.tree = HexagonCover.NBand.M7700_7900.SplitData.node0467 := by
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
  · rfl

def B0461 : Block := .branch 77 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 77992906001238022166532, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 726).pointIds 726), B0462, (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), B0467]
theorem treeEq0461 : B0461.tree = HexagonCover.NBand.M7700_7900.SplitData.node0461 := by
  change Tree.branch (77 : Fin 172) _ = Tree.branch (77 : Fin 172) _
  apply congrArg (Tree.branch (77 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0462
  · rfl
  · rfl
  · rfl
  · exact treeEq0467

def B0468 : Block := .branch 171 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872290776191584849849484802, 40213974138280860456964, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22458641409079416168987859037594559447104] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 740).pointIds 740), (.leaf 3 (Common.fact 734).pointIds 734), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 741).pointIds 741)]
theorem treeEq0468 : B0468.tree = HexagonCover.NBand.M7700_7900.SplitData.node0468 := by
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
  · rfl

def B0460 : Block := .branch 76 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 40213974138280860456964, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 725).pointIds 725), B0461, (.leaf 3 (Common.fact 324).pointIds 324), (.leaf 4 (Common.fact 325).pointIds 325), (.leaf 5 (Common.fact 326).pointIds 326), B0468]
theorem treeEq0460 : B0460.tree = HexagonCover.NBand.M7700_7900.SplitData.node0460 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0461
  · rfl
  · rfl
  · rfl
  · exact treeEq0468

def B0469 : Block := .branch 171 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872290776191584849849484802, 40140187161986022250500, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 22458641409078797123484139597837624672320] ![(.leaf 0 (Common.fact 736).pointIds 736), (.leaf 1 (Common.fact 728).pointIds 728), (.leaf 2 (Common.fact 742).pointIds 742), (.leaf 3 (Common.fact 734).pointIds 734), (.leaf 4 (Common.fact 731).pointIds 731), (.leaf 5 (Common.fact 732).pointIds 732), (.leaf 6 (Common.fact 743).pointIds 743)]
theorem treeEq0469 : B0469.tree = HexagonCover.NBand.M7700_7900.SplitData.node0469 := by
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
  · rfl

def B0459 : Block := .branch 66 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 40140187161986022250500, 8769009823985417509222108996297698117935595282440, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501659789544327283255668651189003870530961472] ![(.leaf 0 (Common.fact 346).pointIds 346), (.leaf 1 (Common.fact 724).pointIds 724), B0460, (.leaf 3 (Common.fact 347).pointIds 347), (.leaf 4 (Common.fact 348).pointIds 348), (.leaf 5 (Common.fact 349).pointIds 349), B0469]
theorem treeEq0459 : B0459.tree = HexagonCover.NBand.M7700_7900.SplitData.node0459 := by
  change Tree.branch (66 : Fin 172) _ = Tree.branch (66 : Fin 172) _
  apply congrArg (Tree.branch (66 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0460
  · rfl
  · rfl
  · rfl
  · exact treeEq0469

def B0458 : Block := .branch 161 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 40149410534022877026308, 5846006549323611672814739330865132078623730196488, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501665234062198335493219132061418221722927168] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 722).pointIds 722), B0459, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 723).pointIds 723)]
theorem treeEq0458 : B0458.tree = HexagonCover.NBand.M7700_7900.SplitData.node0458 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0459
  · rfl
  · rfl
  · rfl

def B0457 : Block := .branch 89 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 40149410534022877026308, 5846006549323611672814739330865132078623730196488, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501665234062198334874249112418728084273365056] ![(.leaf 0 (Common.fact 720).pointIds 720), (.leaf 1 (Common.fact 721).pointIds 721), (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0458]
theorem treeEq0457 : B0457.tree = HexagonCover.NBand.M7700_7900.SplitData.node0457 := by
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
  · exact treeEq0458

def B0456 : Block := .branch 86 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120287872593007646488507143161346, 40149446562819895990276, 5846006549323611672814739330865132078623730196488, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501665234062198334874249112418728084273365056] ![(.leaf 0 (Common.fact 360).pointIds 360), (.leaf 1 (Common.fact 361).pointIds 361), (.leaf 2 (Common.fact 362).pointIds 362), B0457, (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0456 : B0456.tree = HexagonCover.NBand.M7700_7900.SplitData.node0456 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0457
  · rfl
  · rfl
  · rfl

def B0455 : Block := .branch 90 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672814739330865132078623730196488, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501665234062198334874249112418728084273365056] ![(.leaf 0 (Common.fact 713).pointIds 713), B0456, (.leaf 2 (Common.fact 714).pointIds 714), (.leaf 3 (Common.fact 715).pointIds 715), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 717).pointIds 717), (.leaf 6 (Common.fact 718).pointIds 718)]
theorem treeEq0455 : B0455.tree = HexagonCover.NBand.M7700_7900.SplitData.node0455 := by
  change Tree.branch (90 : Fin 172) _ = Tree.branch (90 : Fin 172) _
  apply congrArg (Tree.branch (90 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0456
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0454 : Block := .branch 101 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672814739330865132078623730196488, 182699203488105857128017958444269711768393187344, 233840261972987002208454690542538204970878178295840, 1461501665234062198334874249112418728084273365056] ![B0455, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 712).pointIds 712)]
theorem treeEq0454 : B0454.tree = HexagonCover.NBand.M7700_7900.SplitData.node0454 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0455
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0453 : Block := .branch 143 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672814739330865132078623730196488, 182688053115506591816447190585133387587640197136, 233840261972987002208454690542538204970878178295840, 1461501665234062198334874249112418728084273365056] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0454, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 711).pointIds 711)]
theorem treeEq0453 : B0453.tree = HexagonCover.NBand.M7700_7900.SplitData.node0453 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0454
  · rfl
  · rfl

def B0452 : Block := .branch 129 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672893967493379396416217274146824, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664553497464492997322185669513220736942144] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 710).pointIds 710), (.leaf 5 (Common.fact 123).pointIds 123), B0453]
theorem treeEq0452 : B0452.tree = HexagonCover.NBand.M7700_7900.SplitData.node0452 := by
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
  · exact treeEq0453

def B0451 : Block := .branch 130 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672893967493379396416217274146824, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664553497464492997322185669513220736942144] ![(.leaf 0 (Common.fact 223).pointIds 223), (.leaf 1 (Common.fact 224).pointIds 224), (.leaf 2 (Common.fact 225).pointIds 225), (.leaf 3 (Common.fact 226).pointIds 226), (.leaf 4 (Common.fact 709).pointIds 709), (.leaf 5 (Common.fact 227).pointIds 227), B0452]
theorem treeEq0451 : B0451.tree = HexagonCover.NBand.M7700_7900.SplitData.node0451 := by
  change Tree.branch (130 : Fin 172) _ = Tree.branch (130 : Fin 172) _
  apply congrArg (Tree.branch (130 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0452

def B0450 : Block := .branch 131 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672893967493379396416217274146824, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664553497464492997322185669513220736942144] ![(.leaf 0 (Common.fact 254).pointIds 254), (.leaf 1 (Common.fact 255).pointIds 255), (.leaf 2 (Common.fact 256).pointIds 256), (.leaf 3 (Common.fact 257).pointIds 257), (.leaf 4 (Common.fact 708).pointIds 708), (.leaf 5 (Common.fact 258).pointIds 258), B0451]
theorem treeEq0450 : B0450.tree = HexagonCover.NBand.M7700_7900.SplitData.node0450 := by
  change Tree.branch (131 : Fin 172) _ = Tree.branch (131 : Fin 172) _
  apply congrArg (Tree.branch (131 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0451

theorem accepted0450 : B0450.accepted = true := by decide +kernel
theorem checked0450 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0450 (maskNeeds ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672893967493379396416217274146824, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664553497464492997322185669513220736942144]) := by
  rw [← treeEq0450]
  exact B0450.sound accepted0450
#print axioms checked0450

def Tip0430_0450 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0450 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 40149446562819895990276, 5846006549323611672893967493379396416217274146824, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664553497464492997322185669513220736942144] checked0450
def B0449 : Block := .branch 75 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 5846006549323611672894006179005624084350864744456, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 424).pointIds 424), (.leaf 1 (Common.fact 425).pointIds 425), Tip0430_0450, (.leaf 3 (Common.fact 618).pointIds 618), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 428).pointIds 428), (.leaf 6 (Common.fact 707).pointIds 707)]
theorem treeEq0449 : B0449.tree = HexagonCover.NBand.M7700_7900.SplitData.node0449 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0448 : Block := .branch 162 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0449, (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 706).pointIds 706)]
theorem treeEq0448 : B0448.tree = HexagonCover.NBand.M7700_7900.SplitData.node0448 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0449
  · rfl
  · rfl
  · rfl

def B0447 : Block := .branch 163 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 185546032992355781988429627480012479166890999824, 233840261972987002208454690542538204970878178295840, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 704).pointIds 704), (.leaf 5 (Common.fact 291).pointIds 291), B0448]
theorem treeEq0447 : B0447.tree = HexagonCover.NBand.M7700_7900.SplitData.node0447 := by
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
  · exact treeEq0448

def B0446 : Block := .branch 165 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 185546032992355781988429627480012479166890999824, 187072209578398108825936775895617148341888336920608, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 703).pointIds 703), B0447, (.leaf 0 [] 0)]
theorem treeEq0446 : B0446.tree = HexagonCover.NBand.M7700_7900.SplitData.node0446 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0447
  · rfl

def B0445 : Block := .branch 167 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 185546032992355781988429627480012479166890999824, 42535295865117307932921825928971419680, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 702).pointIds 702), B0446, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0445 : B0445.tree = HexagonCover.NBand.M7700_7900.SplitData.node0445 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0446
  · rfl

def B0444 : Block := .branch 151 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 182691537606943862226313055541113488894125506576, 42535295865117307932921825928971419680, 1461501664558814376476136985677284741461858320448] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), B0445, (.leaf 5 (Common.fact 496).pointIds 496), (.leaf 6 (Common.fact 701).pointIds 701)]
theorem treeEq0444 : B0444.tree = HexagonCover.NBand.M7700_7900.SplitData.node0444 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0445
  · rfl
  · rfl

def B0443 : Block := .branch 160 ![1496577676626844588240573268702064107938033629659521, 748288838313422294120286634652968361108232244037122, 2370514699862734280708, 79266848140492005727134572552, 182691537606943862226313055541113488894125506576, 42535295865117307932921825928971419680, 27227911458272452152961001721805925777472] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 699).pointIds 699), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0444]
theorem treeEq0443 : B0443.tree = HexagonCover.NBand.M7700_7900.SplitData.node0443 := by
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
  · exact treeEq0444

def B0442 : Block := .branch 169 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184118785299649822107371341510562984030508253200, 5708990813359135389350451810719806474502406176, 27227911458272452152961001721805925777472] ![(.leaf 0 (Common.fact 647).pointIds 647), B0443, (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 698).pointIds 698)]
theorem treeEq0442 : B0442.tree = HexagonCover.NBand.M7700_7900.SplitData.node0442 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0443
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0441 : Block := .branch 132 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184118785299649822107371341510562984030508253200, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 207).pointIds 207), B0442]
theorem treeEq0441 : B0441.tree = HexagonCover.NBand.M7700_7900.SplitData.node0441 := by
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
  · exact treeEq0442

def B0440 : Block := .branch 138 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184118436850506095066384755014964973899859722256, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0441, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 693).pointIds 693)]
theorem treeEq0440 : B0440.tree = HexagonCover.NBand.M7700_7900.SplitData.node0440 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0441
  · rfl
  · rfl

def B0439 : Block := .branch 133 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184118436850506095066384755014964973899859722256, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 692).pointIds 692), (.leaf 5 (Common.fact 166).pointIds 166), B0440]
theorem treeEq0439 : B0439.tree = HexagonCover.NBand.M7700_7900.SplitData.node0439 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0440

def B0438 : Block := .branch 139 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184117739952218640984411582023768953638562660368, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0439, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0438 : B0438.tree = HexagonCover.NBand.M7700_7900.SplitData.node0438 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0439
  · rfl
  · rfl

def B0437 : Block := .branch 140 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184117739952218640984411582023768953638562660368, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0438, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 685).pointIds 685)]
theorem treeEq0437 : B0437.tree = HexagonCover.NBand.M7700_7900.SplitData.node0437 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0438
  · rfl
  · rfl

def B0436 : Block := .branch 141 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990813359135389350451810719806474502406176, 21783393587537436737547008002897634394176] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0437, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 684).pointIds 684)]
theorem treeEq0436 : B0436.tree = HexagonCover.NBand.M7700_7900.SplitData.node0436 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0437
  · rfl
  · rfl

def B0435 : Block := .branch 112 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990813359135389350451810719806474502406176, 21783388395240578202719379472401305174080] ![(.leaf 0 (Common.fact 683).pointIds 683), (.leaf 1 (Common.fact 500).pointIds 500), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 502).pointIds 502), (.leaf 4 (Common.fact 503).pointIds 503), (.leaf 5 (Common.fact 504).pointIds 504), B0436]
theorem treeEq0435 : B0435.tree = HexagonCover.NBand.M7700_7900.SplitData.node0435 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0436

def B0434 : Block := .branch 122 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 184114952359068824656518890058984872593374412816, 5708990813359135389350451810719806474502406176, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 471).pointIds 471), (.leaf 1 (Common.fact 472).pointIds 472), (.leaf 2 (Common.fact 473).pointIds 473), (.leaf 3 (Common.fact 474).pointIds 474), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 476).pointIds 476), B0435]
theorem treeEq0434 : B0434.tree = HexagonCover.NBand.M7700_7900.SplitData.node0434 := by
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
  · exact treeEq0435

def B0433 : Block := .branch 157 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990813359135389350451810719806474502406176, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0434, (.leaf 5 (Common.fact 470).pointIds 470), (.leaf 0 [] 0)]
theorem treeEq0433 : B0433.tree = HexagonCover.NBand.M7700_7900.SplitData.node0433 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0434
  · rfl
  · rfl

def B0432 : Block := .branch 125 ![1496577676626844588240573268702064107938033629659521, 302231455044394782033410, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 682).pointIds 682), (.leaf 1 (Common.fact 465).pointIds 465), (.leaf 2 (Common.fact 466).pointIds 466), (.leaf 3 (Common.fact 467).pointIds 467), (.leaf 4 (Common.fact 468).pointIds 468), B0433, (.leaf 6 (Common.fact 469).pointIds 469)]
theorem treeEq0432 : B0432.tree = HexagonCover.NBand.M7700_7900.SplitData.node0432 := by
  change Tree.branch (125 : Fin 172) _ = Tree.branch (125 : Fin 172) _
  apply congrArg (Tree.branch (125 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0433
  · rfl

def B0431 : Block := .branch 170 ![590295810358705652097, 302231599159582857889282, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0432, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0431 : B0431.tree = HexagonCover.NBand.M7700_7900.SplitData.node0431 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0432
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0430 : Block := .branch 88 ![590295810358705652097, 302231599159582857889282, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 681).pointIds 681), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0431]
theorem treeEq0430 : B0430.tree = HexagonCover.NBand.M7700_7900.SplitData.node0430 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0431

theorem accepted0430 : B0430.accepted = true := by decide +kernel
theorem checked0430 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0430 (maskNeeds ![590295810358705652097, 302231599159582857889282, 2370514699862734280708, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0430]
  exact B0430.sound accepted0430
#print axioms checked0430

def B0495 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995953122419862861159358529600] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 775).pointIds 775), (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 776).pointIds 776)]
theorem treeEq0495 : B0495.tree = HexagonCover.NBand.M7700_7900.SplitData.node0495 := by
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

def B0494 : Block := .branch 89 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 773).pointIds 773), (.leaf 1 (Common.fact 774).pointIds 774), (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0495]
theorem treeEq0494 : B0494.tree = HexagonCover.NBand.M7700_7900.SplitData.node0494 := by
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
  · exact treeEq0495

def B0493 : Block := .branch 159 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 767).pointIds 767), (.leaf 1 (Common.fact 768).pointIds 768), (.leaf 2 (Common.fact 769).pointIds 769), (.leaf 3 (Common.fact 770).pointIds 770), (.leaf 4 (Common.fact 771).pointIds 771), (.leaf 5 (Common.fact 772).pointIds 772), B0494]
theorem treeEq0493 : B0493.tree = HexagonCover.NBand.M7700_7900.SplitData.node0493 := by
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
  · exact treeEq0494

def B0492 : Block := .branch 124 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![B0493, (.leaf 1 (Common.fact 150).pointIds 150), (.leaf 2 (Common.fact 151).pointIds 151), (.leaf 3 (Common.fact 152).pointIds 152), (.leaf 4 (Common.fact 153).pointIds 153), (.leaf 5 (Common.fact 154).pointIds 154), (.leaf 6 (Common.fact 766).pointIds 766)]
theorem treeEq0492 : B0492.tree = HexagonCover.NBand.M7700_7900.SplitData.node0492 := by
  change Tree.branch (124 : Fin 172) _ = Tree.branch (124 : Fin 172) _
  apply congrArg (Tree.branch (124 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0493
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0491 : Block := .branch 128 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0492, (.leaf 4 (Common.fact 764).pointIds 764), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 765).pointIds 765)]
theorem treeEq0491 : B0491.tree = HexagonCover.NBand.M7700_7900.SplitData.node0491 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0492
  · rfl
  · rfl
  · rfl

def B0490 : Block := .branch 138 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0491, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0490 : B0490.tree = HexagonCover.NBand.M7700_7900.SplitData.node0490 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0491
  · rfl
  · rfl

def B0489 : Block := .branch 139 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0490, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0489 : B0489.tree = HexagonCover.NBand.M7700_7900.SplitData.node0489 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0490
  · rfl
  · rfl

def B0488 : Block := .branch 140 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0489, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0488 : B0488.tree = HexagonCover.NBand.M7700_7900.SplitData.node0488 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0489
  · rfl
  · rfl

def B0487 : Block := .branch 141 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 6148, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 21922524581741615255995334152400220171021908967488] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0488, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 760).pointIds 760)]
theorem treeEq0487 : B0487.tree = HexagonCover.NBand.M7700_7900.SplitData.node0487 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0488
  · rfl
  · rfl

def B0486 : Block := .branch 160 ![1496577676626844588243108569902520566741027036070273, 748288838313422294120286634350736906204574950360578, 9295429630892709892, 79228162514264337593543974920, 11150372599265311570767859136324180753088528, 393248, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 759).pointIds 759), (.leaf 2 (Common.fact 700).pointIds 700), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0487]
theorem treeEq0486 : B0486.tree = HexagonCover.NBand.M7700_7900.SplitData.node0486 := by
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
  · exact treeEq0487

def B0485 : Block := .branch 169 ![1496577676626844588243108569902520566741027036070273, 140737488356866, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![(.leaf 0 (Common.fact 757).pointIds 757), B0486, (.leaf 2 (Common.fact 695).pointIds 695), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0485 : B0485.tree = HexagonCover.NBand.M7700_7900.SplitData.node0485 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0486
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0484 : Block := .branch 170 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266848140492005727134572552, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712338108561969740994501740152225856] ![B0485, (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 673).pointIds 673), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0484 : B0484.tree = HexagonCover.NBand.M7700_7900.SplitData.node0484 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0485
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0483 : Block := .branch 162 ![2535301201046754613352112062849, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 754).pointIds 754), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0484]
theorem treeEq0483 : B0483.tree = HexagonCover.NBand.M7700_7900.SplitData.node0483 := by
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
  · exact treeEq0484

def B0482 : Block := .branch 101 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0483, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0482 : B0482.tree = HexagonCover.NBand.M7700_7900.SplitData.node0482 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0483
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0481 : Block := .branch 163 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0482]
theorem treeEq0481 : B0481.tree = HexagonCover.NBand.M7700_7900.SplitData.node0481 := by
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
  · exact treeEq0482

def B0480 : Block := .branch 165 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0481, (.leaf 0 [] 0)]
theorem treeEq0480 : B0480.tree = HexagonCover.NBand.M7700_7900.SplitData.node0480 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0481
  · rfl

def B0479 : Block := .branch 167 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0480, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0479 : B0479.tree = HexagonCover.NBand.M7700_7900.SplitData.node0479 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0480
  · rfl

def B0478 : Block := .branch 143 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0479, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0478 : B0478.tree = HexagonCover.NBand.M7700_7900.SplitData.node0478 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0479
  · rfl
  · rfl

def B0477 : Block := .branch 144 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0478, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0477 : B0477.tree = HexagonCover.NBand.M7700_7900.SplitData.node0477 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0478
  · rfl

def B0476 : Block := .branch 161 ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 722).pointIds 722), (.leaf 3 (Common.fact 747).pointIds 747), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0477]
theorem treeEq0476 : B0476.tree = HexagonCover.NBand.M7700_7900.SplitData.node0476 := by
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
  · exact treeEq0477

theorem accepted0476 : B0476.accepted = true := by decide +kernel
theorem checked0476 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0476 (maskNeeds ![590295810358705652097, 144255925564212738, 9295429630892709892, 79266867029957937205715427336, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192]) := by
  rw [← treeEq0476]
  exact B0476.sound accepted0476
#print axioms checked0476

end HexagonCover.NBand.M7700_7900.SplitTree.Run0005
