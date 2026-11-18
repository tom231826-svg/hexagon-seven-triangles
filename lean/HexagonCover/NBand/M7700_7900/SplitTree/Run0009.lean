import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0007
import HexagonCover.NBand.M7700_7900.SplitTree.Run0008
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0009
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0661_0664 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0664 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0008.checked0664
def B0730 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 3013616376198099888818938186722631561406715824439360] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M7700_7900.SplitData.node0730 := by
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

def B0729 : Block := .branch 171 ![1496577676626844588243108569901930270930668330418561, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0730]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M7700_7900.SplitData.node0729 := by
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
  · exact treeEq0730

def B0728 : Block := .branch 170 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![B0729, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M7700_7900.SplitData.node0728 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0729
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0727 : Block := .branch 162 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100664976909988818805072742246252608] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 782).pointIds 782), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0728]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M7700_7900.SplitData.node0727 := by
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
  · exact treeEq0728

def B0726 : Block := .branch 101 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0727, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M7700_7900.SplitData.node0726 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0727
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0725 : Block := .branch 163 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0726]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M7700_7900.SplitData.node0725 := by
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
  · exact treeEq0726

def B0724 : Block := .branch 165 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0725, (.leaf 0 [] 0)]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M7700_7900.SplitData.node0724 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0725
  · rfl

def B0723 : Block := .branch 167 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0724, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M7700_7900.SplitData.node0723 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0724
  · rfl

def B0722 : Block := .branch 143 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0723, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M7700_7900.SplitData.node0722 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0721 : Block := .branch 144 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0722, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M7700_7900.SplitData.node0721 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0722
  · rfl

def B0720 : Block := .branch 161 ![385, 144115188075857410, 9223512774343137284, 38687987410909568413229064, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0721]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M7700_7900.SplitData.node0720 := by
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
  · exact treeEq0721

def B0663 : Block := .branch 71 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), Tip0661_0664, B0720, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0663 : B0663.tree = HexagonCover.NBand.M7700_7900.SplitData.node0663 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0720
  · rfl
  · rfl
  · rfl

def B0734 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 10889035741470030830827987437816582864912, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 825).pointIds 825), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M7700_7900.SplitData.node0734 := by
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

def B0733 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2993155353275467247964403666457313141107030983442496] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), B0734, (.leaf 5 (Common.fact 166).pointIds 166), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M7700_7900.SplitData.node0733 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0734
  · rfl
  · rfl

def B0732 : Block := .branch 171 ![1496577676626844588240573268701473812127674924007809, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0733]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M7700_7900.SplitData.node0732 := by
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
  · exact treeEq0733

def B0731 : Block := .branch 170 ![385, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054365516851681135427648] ![B0732, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M7700_7900.SplitData.node0731 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0732
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0662 : Block := .branch 67 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 167).pointIds 167), B0663, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), B0731]
theorem treeEq0662 : B0662.tree = HexagonCover.NBand.M7700_7900.SplitData.node0662 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0663
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0731

def B0736 : Block := .branch 170 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M7700_7900.SplitData.node0736 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0735 : Block := .branch 171 ![385, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B0736, (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M7700_7900.SplitData.node0735 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0736
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0661 : Block := .branch 65 ![385, 1008806316530992642, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 828).pointIds 828), B0662, (.leaf 3 (Common.fact 453).pointIds 453), (.leaf 4 (Common.fact 454).pointIds 454), (.leaf 5 (Common.fact 455).pointIds 455), B0735]
theorem treeEq0661 : B0661.tree = HexagonCover.NBand.M7700_7900.SplitData.node0661 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0662
  · rfl
  · rfl
  · rfl
  · exact treeEq0735

theorem accepted0661 : B0661.accepted = true := by decide +kernel
theorem checked0661 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0661 (maskNeeds ![385, 1008806316530992642, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0661]
  exact B0661.sound accepted0661
#print axioms checked0661

def Tip0576_0586 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0586 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0008.checked0586
def B0578 : Block := .branch 170 ![288230376151712129, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403666457165567154441307029568] ![(.leaf 0 (Common.fact 671).pointIds 671), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M7700_7900.SplitData.node0578 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0577 : Block := .branch 171 ![288230376151712129, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 797).pointIds 797), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0578]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M7700_7900.SplitData.node0577 := by
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
  · exact treeEq0578

def B0582 : Block := .branch 170 ![576460752303423873, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403666457165567154441307029568] ![(.leaf 0 (Common.fact 678).pointIds 678), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M7700_7900.SplitData.node0582 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0581 : Block := .branch 171 ![576460752303423873, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0582]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M7700_7900.SplitData.node0581 := by
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
  · exact treeEq0582

def B0647 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692013098647223345629478661730264157247460442128, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 662).pointIds 662), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq0647 : B0647.tree = HexagonCover.NBand.M7700_7900.SplitData.node0647 := by
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

def B0646 : Block := .branch 163 ![385, 1538, 6148, 24584, 98320, 393248, 21778071483257129054808238709450164666432] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0647, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0646 : B0646.tree = HexagonCover.NBand.M7700_7900.SplitData.node0646 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0647
  · rfl
  · rfl

def B0645 : Block := .branch 170 ![385, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054808238709450164666432] ![B0646, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq0645 : B0645.tree = HexagonCover.NBand.M7700_7900.SplitData.node0645 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0646
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0585 : Block := .branch 69 ![385, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![Tip0576_0586, (.leaf 1 (Common.fact 459).pointIds 459), (.leaf 2 (Common.fact 460).pointIds 460), (.leaf 3 (Common.fact 461).pointIds 461), (.leaf 4 (Common.fact 462).pointIds 462), (.leaf 5 (Common.fact 463).pointIds 463), B0645]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M7700_7900.SplitData.node0585 := by
  change Tree.branch (69 : Fin 172) _ = Tree.branch (69 : Fin 172) _
  apply congrArg (Tree.branch (69 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0645

def B0651 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 10889035741470030830827987437816582864912, 393248, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 825).pointIds 825), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 666).pointIds 666)]
theorem treeEq0651 : B0651.tree = HexagonCover.NBand.M7700_7900.SplitData.node0651 := by
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

def B0650 : Block := .branch 133 ![385, 1538, 6148, 38685626227668133590622216, 98320, 393248, 2993155353275467247964403666457313141107030983442496] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), B0651, (.leaf 5 (Common.fact 166).pointIds 166), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0650 : B0650.tree = HexagonCover.NBand.M7700_7900.SplitData.node0650 := by
  change Tree.branch (133 : Fin 172) _ = Tree.branch (133 : Fin 172) _
  apply congrArg (Tree.branch (133 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0651
  · rfl
  · rfl

def B0649 : Block := .branch 171 ![1496577676626844588240573268701473812127674924007809, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054365516851681135427648] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0650]
theorem treeEq0649 : B0649.tree = HexagonCover.NBand.M7700_7900.SplitData.node0649 := by
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
  · exact treeEq0650

def B0648 : Block := .branch 170 ![385, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054365516851681135427648] ![B0649, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 784).pointIds 784)]
theorem treeEq0648 : B0648.tree = HexagonCover.NBand.M7700_7900.SplitData.node0648 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0649
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0584 : Block := .branch 67 ![385, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 167).pointIds 167), B0585, (.leaf 2 (Common.fact 168).pointIds 168), (.leaf 3 (Common.fact 169).pointIds 169), (.leaf 4 (Common.fact 170).pointIds 170), (.leaf 5 (Common.fact 171).pointIds 171), B0648]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M7700_7900.SplitData.node0584 := by
  change Tree.branch (67 : Fin 172) _ = Tree.branch (67 : Fin 172) _
  apply congrArg (Tree.branch (67 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0585
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0648

def B0653 : Block := .branch 170 ![2993155353253689176481146537402947624255349848015233, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq0653 : B0653.tree = HexagonCover.NBand.M7700_7900.SplitData.node0653 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0652 : Block := .branch 171 ![385, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311749925714704515727424] ![B0653, (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0652 : B0652.tree = HexagonCover.NBand.M7700_7900.SplitData.node0652 := by
  change Tree.branch (171 : Fin 172) _ = Tree.branch (171 : Fin 172) _
  apply congrArg (Tree.branch (171 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0653
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0583 : Block := .branch 65 ![385, 1080863910568920578, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 451).pointIds 451), (.leaf 1 (Common.fact 452).pointIds 452), B0584, (.leaf 3 (Common.fact 453).pointIds 453), (.leaf 4 (Common.fact 454).pointIds 454), (.leaf 5 (Common.fact 455).pointIds 455), B0652]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M7700_7900.SplitData.node0583 := by
  change Tree.branch (65 : Fin 172) _ = Tree.branch (65 : Fin 172) _
  apply congrArg (Tree.branch (65 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0584
  · rfl
  · rfl
  · rfl
  · exact treeEq0652

def B0580 : Block := .branch 59 ![385, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0581, B0583, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M7700_7900.SplitData.node0580 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0581
  · exact treeEq0583
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0579 : Block := .branch 64 ![385, 504403158265497090, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 215).pointIds 215), B0580, (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M7700_7900.SplitData.node0579 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0580
  · rfl
  · rfl
  · rfl
  · rfl

def B0576 : Block := .branch 58 ![385, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0577, B0579, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 148).pointIds 148)]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M7700_7900.SplitData.node0576 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0577
  · exact treeEq0579
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0576 : B0576.accepted = true := by decide +kernel
theorem checked0576 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0576 (maskNeeds ![385, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0576]
  exact B0576.sound accepted0576
#print axioms checked0576

def Tip0565_0661 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0661 ![385, 1008806316530992642, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0661
def Tip0565_0576 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0576 ![385, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0576
def B0574 : Block := .branch 58 ![1496577676626844588240573268701473812127674924007809, 180143985094821378, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 671).pointIds 671), (.leaf 1 (Common.fact 796).pointIds 796), (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 148).pointIds 148)]
theorem treeEq0574 : B0574.tree = HexagonCover.NBand.M7700_7900.SplitData.node0574 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0573 : Block := .branch 170 ![385, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 1461501659108974401460813886934225918747391557696] ![B0574, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 795).pointIds 795)]
theorem treeEq0573 : B0573.tree = HexagonCover.NBand.M7700_7900.SplitData.node0573 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0574
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0572 : Block := .branch 160 ![385, 180143985094821378, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 791).pointIds 791), (.leaf 2 (Common.fact 792).pointIds 792), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), B0573]
theorem treeEq0572 : B0572.tree = HexagonCover.NBand.M7700_7900.SplitData.node0572 := by
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
  · exact treeEq0573

def B0656 : Block := .branch 170 ![288230376151712129, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403666457165567154441307029568] ![(.leaf 0 (Common.fact 671).pointIds 671), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0656 : B0656.tree = HexagonCover.NBand.M7700_7900.SplitData.node0656 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0655 : Block := .branch 171 ![288230376151712129, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 797).pointIds 797), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0656]
theorem treeEq0655 : B0655.tree = HexagonCover.NBand.M7700_7900.SplitData.node0655 := by
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
  · exact treeEq0656

def B0660 : Block := .branch 170 ![576460752303423873, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403666457165567154441307029568] ![(.leaf 0 (Common.fact 678).pointIds 678), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 803).pointIds 803)]
theorem treeEq0660 : B0660.tree = HexagonCover.NBand.M7700_7900.SplitData.node0660 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0659 : Block := .branch 171 ![576460752303423873, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0660]
theorem treeEq0659 : B0659.tree = HexagonCover.NBand.M7700_7900.SplitData.node0659 := by
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
  · exact treeEq0660

def B0658 : Block := .branch 59 ![385, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0659, Tip0565_0661, (.leaf 2 (Common.fact 216).pointIds 216), (.leaf 3 (Common.fact 217).pointIds 217), (.leaf 4 (Common.fact 218).pointIds 218), (.leaf 5 (Common.fact 219).pointIds 219), (.leaf 6 (Common.fact 220).pointIds 220)]
theorem treeEq0658 : B0658.tree = HexagonCover.NBand.M7700_7900.SplitData.node0658 := by
  change Tree.branch (59 : Fin 172) _ = Tree.branch (59 : Fin 172) _
  apply congrArg (Tree.branch (59 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0659
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0657 : Block := .branch 64 ![385, 432345564227569154, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 173).pointIds 173), (.leaf 1 (Common.fact 827).pointIds 827), B0658, (.leaf 3 (Common.fact 175).pointIds 175), (.leaf 4 (Common.fact 176).pointIds 176), (.leaf 5 (Common.fact 177).pointIds 177), (.leaf 6 (Common.fact 178).pointIds 178)]
theorem treeEq0657 : B0657.tree = HexagonCover.NBand.M7700_7900.SplitData.node0657 := by
  change Tree.branch (64 : Fin 172) _ = Tree.branch (64 : Fin 172) _
  apply congrArg (Tree.branch (64 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0658
  · rfl
  · rfl
  · rfl
  · rfl

def B0654 : Block := .branch 58 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0655, B0657, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 148).pointIds 148)]
theorem treeEq0654 : B0654.tree = HexagonCover.NBand.M7700_7900.SplitData.node0654 := by
  change Tree.branch (58 : Fin 172) _ = Tree.branch (58 : Fin 172) _
  apply congrArg (Tree.branch (58 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0655
  · exact treeEq0657
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0575 : Block := .branch 56 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 139).pointIds 139), Tip0565_0576, B0654, (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 143).pointIds 143)]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M7700_7900.SplitData.node0575 := by
  change Tree.branch (56 : Fin 172) _ = Tree.branch (56 : Fin 172) _
  apply congrArg (Tree.branch (56 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0654
  · rfl
  · rfl
  · rfl
  · rfl

def B0571 : Block := .branch 55 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 71).pointIds 71), B0572, B0575, (.leaf 3 (Common.fact 72).pointIds 72), (.leaf 4 (Common.fact 73).pointIds 73), (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 75).pointIds 75)]
theorem treeEq0571 : B0571.tree = HexagonCover.NBand.M7700_7900.SplitData.node0571 := by
  change Tree.branch (55 : Fin 172) _ = Tree.branch (55 : Fin 172) _
  apply congrArg (Tree.branch (55 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0572
  · exact treeEq0575
  · rfl
  · rfl
  · rfl
  · rfl

def B0570 : Block := .branch 103 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![B0571, (.leaf 1 (Common.fact 94).pointIds 94), (.leaf 2 (Common.fact 95).pointIds 95), (.leaf 3 (Common.fact 96).pointIds 96), (.leaf 4 (Common.fact 97).pointIds 97), (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 790).pointIds 790)]
theorem treeEq0570 : B0570.tree = HexagonCover.NBand.M7700_7900.SplitData.node0570 := by
  change Tree.branch (103 : Fin 172) _ = Tree.branch (103 : Fin 172) _
  apply congrArg (Tree.branch (103 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0571
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0569 : Block := .branch 150 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), B0570, (.leaf 5 (Common.fact 110).pointIds 110), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0569 : B0569.tree = HexagonCover.NBand.M7700_7900.SplitData.node0569 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0570
  · rfl
  · rfl

def B0568 : Block := .branch 98 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 98320, 5708990770823839524233143877797980545531379744, 21778071482940216404160885548717283213376] ![(.leaf 0 (Common.fact 131).pointIds 131), (.leaf 1 (Common.fact 132).pointIds 132), (.leaf 2 (Common.fact 133).pointIds 133), (.leaf 3 (Common.fact 134).pointIds 134), (.leaf 4 (Common.fact 135).pointIds 135), (.leaf 5 (Common.fact 136).pointIds 136), B0569]
theorem treeEq0568 : B0568.tree = HexagonCover.NBand.M7700_7900.SplitData.node0568 := by
  change Tree.branch (98 : Fin 172) _ = Tree.branch (98 : Fin 172) _
  apply congrArg (Tree.branch (98 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0569

def B0567 : Block := .branch 85 ![385, 144115188075857410, 9223512774343137284, 79228162514264337593543974920, 98320, 5708990770823839524233143877797980545531379744, 21778071482940216404160885548717283213376] ![(.leaf 0 (Common.fact 125).pointIds 125), (.leaf 1 (Common.fact 126).pointIds 126), (.leaf 2 (Common.fact 789).pointIds 789), B0568, (.leaf 4 (Common.fact 128).pointIds 128), (.leaf 5 (Common.fact 129).pointIds 129), (.leaf 6 (Common.fact 130).pointIds 130)]
theorem treeEq0567 : B0567.tree = HexagonCover.NBand.M7700_7900.SplitData.node0567 := by
  change Tree.branch (85 : Fin 172) _ = Tree.branch (85 : Fin 172) _
  apply congrArg (Tree.branch (85 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0568
  · rfl
  · rfl
  · rfl

def B0566 : Block := .branch 152 ![385, 144115188075857410, 9223512774343137284, 79228162514264337593543974920, 98320, 393248, 21778071482940216404160885548717283213376] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), B0567, (.leaf 6 (Common.fact 788).pointIds 788)]
theorem treeEq0566 : B0566.tree = HexagonCover.NBand.M7700_7900.SplitData.node0566 := by
  change Tree.branch (152 : Fin 172) _ = Tree.branch (152 : Fin 172) _
  apply congrArg (Tree.branch (152 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0567
  · rfl

def B0565 : Block := .branch 87 ![385, 144115188075857410, 9223512774343137284, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 328).pointIds 328), (.leaf 1 (Common.fact 329).pointIds 329), (.leaf 2 (Common.fact 787).pointIds 787), (.leaf 3 (Common.fact 331).pointIds 331), (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B0566]
theorem treeEq0565 : B0565.tree = HexagonCover.NBand.M7700_7900.SplitData.node0565 := by
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
  · exact treeEq0566

theorem accepted0565 : B0565.accepted = true := by decide +kernel
theorem checked0565 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0565 (maskNeeds ![385, 144115188075857410, 9223512774343137284, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848]) := by
  rw [← treeEq0565]
  exact B0565.sound accepted0565
#print axioms checked0565

def Tip0001_0021 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0021 ![385, 144255925564212738, 9277485601127405572, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] HexagonCover.NBand.M7700_7900.SplitTree.Run0007.checked0021
def Tip0001_0565 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0565 ![385, 144115188075857410, 9223512774343137284, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] checked0565
def B0020 : Block := .branch 129 ![385, 1538, 6148, 79228162514264337593543974920, 5575186299632655785383929568162090376593424, 393248, 21778071482940371448897251124908939280448] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 122).pointIds 122), (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 124).pointIds 124)]
theorem treeEq0020 : B0020.tree = HexagonCover.NBand.M7700_7900.SplitData.node0020 := by
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

def B0019 : Block := .branch 142 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371448897251124908939280448] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), (.leaf 3 (Common.fact 115).pointIds 115), B0020, (.leaf 5 (Common.fact 116).pointIds 116), (.leaf 6 (Common.fact 117).pointIds 117)]
theorem treeEq0019 : B0019.tree = HexagonCover.NBand.M7700_7900.SplitData.node0019 := by
  change Tree.branch (142 : Fin 172) _ = Tree.branch (142 : Fin 172) _
  apply congrArg (Tree.branch (142 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0020
  · rfl
  · rfl

def B0018 : Block := .branch 150 ![385, 1538, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371448897251124908939280448] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), B0019, (.leaf 5 (Common.fact 110).pointIds 110), (.leaf 6 (Common.fact 111).pointIds 111)]
theorem treeEq0018 : B0018.tree = HexagonCover.NBand.M7700_7900.SplitData.node0018 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0019
  · rfl
  · rfl

def B0017 : Block := .branch 78 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0018]
theorem treeEq0017 : B0017.tree = HexagonCover.NBand.M7700_7900.SplitData.node0017 := by
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
  · exact treeEq0018

def B0016 : Block := .branch 103 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371146665796221251645603904] ![B0017, (.leaf 1 (Common.fact 94).pointIds 94), (.leaf 2 (Common.fact 95).pointIds 95), (.leaf 3 (Common.fact 96).pointIds 96), (.leaf 4 (Common.fact 97).pointIds 97), (.leaf 5 (Common.fact 98).pointIds 98), (.leaf 6 (Common.fact 99).pointIds 99)]
theorem treeEq0016 : B0016.tree = HexagonCover.NBand.M7700_7900.SplitData.node0016 := by
  change Tree.branch (103 : Fin 172) _ = Tree.branch (103 : Fin 172) _
  apply congrArg (Tree.branch (103 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0017
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0015 : Block := .branch 147 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 89).pointIds 89), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), B0016, (.leaf 5 (Common.fact 92).pointIds 92), (.leaf 6 (Common.fact 93).pointIds 93)]
theorem treeEq0015 : B0015.tree = HexagonCover.NBand.M7700_7900.SplitData.node0015 := by
  change Tree.branch (147 : Fin 172) _ = Tree.branch (147 : Fin 172) _
  apply congrArg (Tree.branch (147 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0016
  · rfl
  · rfl

def B0014 : Block := .branch 152 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940371146665796221251645603904] ![(.leaf 0 (Common.fact 82).pointIds 82), (.leaf 1 (Common.fact 83).pointIds 83), (.leaf 2 (Common.fact 84).pointIds 84), (.leaf 3 (Common.fact 85).pointIds 85), (.leaf 4 (Common.fact 86).pointIds 86), B0015, (.leaf 6 (Common.fact 87).pointIds 87)]
theorem treeEq0014 : B0014.tree = HexagonCover.NBand.M7700_7900.SplitData.node0014 := by
  change Tree.branch (152 : Fin 172) _ = Tree.branch (152 : Fin 172) _
  apply congrArg (Tree.branch (152 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0015
  · rfl

def B0013 : Block := .branch 88 ![385, 180143985094821378, 6148, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0014]
theorem treeEq0013 : B0013.tree = HexagonCover.NBand.M7700_7900.SplitData.node0013 := by
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
  · exact treeEq0014

def B0012 : Block := .branch 55 ![385, 144255925564212738, 9241456804108441604, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 71).pointIds 71), B0013, Tip0001_0021, (.leaf 3 (Common.fact 72).pointIds 72), (.leaf 4 (Common.fact 73).pointIds 73), (.leaf 5 (Common.fact 74).pointIds 74), (.leaf 6 (Common.fact 75).pointIds 75)]
theorem treeEq0012 : B0012.tree = HexagonCover.NBand.M7700_7900.SplitData.node0012 := by
  change Tree.branch (55 : Fin 172) _ = Tree.branch (55 : Fin 172) _
  apply congrArg (Tree.branch (55 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0013
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0011 : Block := .branch 47 ![385, 144115188075857410, 9241456804108441604, 79228162514264337593543974920, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 66).pointIds 66), B0012, Tip0001_0565, (.leaf 3 (Common.fact 67).pointIds 67), (.leaf 4 (Common.fact 68).pointIds 68), (.leaf 5 (Common.fact 69).pointIds 69), (.leaf 6 (Common.fact 70).pointIds 70)]
theorem treeEq0011 : B0011.tree = HexagonCover.NBand.M7700_7900.SplitData.node0011 := by
  change Tree.branch (47 : Fin 172) _ = Tree.branch (47 : Fin 172) _
  apply congrArg (Tree.branch (47 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0012
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0010 : Block := .branch 96 ![385, 144115188075857410, 9241456804108441604, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 60).pointIds 60), (.leaf 1 (Common.fact 61).pointIds 61), (.leaf 2 (Common.fact 62).pointIds 62), B0011, (.leaf 4 (Common.fact 63).pointIds 63), (.leaf 5 (Common.fact 64).pointIds 64), (.leaf 6 (Common.fact 65).pointIds 65)]
theorem treeEq0010 : B0010.tree = HexagonCover.NBand.M7700_7900.SplitData.node0010 := by
  change Tree.branch (96 : Fin 172) _ = Tree.branch (96 : Fin 172) _
  apply congrArg (Tree.branch (96 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0011
  · rfl
  · rfl
  · rfl

def B0009 : Block := .branch 46 ![385, 144115188075857410, 9241386435364263940, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 54).pointIds 54), (.leaf 1 (Common.fact 55).pointIds 55), B0010, (.leaf 3 (Common.fact 56).pointIds 56), (.leaf 4 (Common.fact 57).pointIds 57), (.leaf 5 (Common.fact 58).pointIds 58), (.leaf 6 (Common.fact 59).pointIds 59)]
theorem treeEq0009 : B0009.tree = HexagonCover.NBand.M7700_7900.SplitData.node0009 := by
  change Tree.branch (46 : Fin 172) _ = Tree.branch (46 : Fin 172) _
  apply congrArg (Tree.branch (46 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0010
  · rfl
  · rfl
  · rfl
  · rfl

def B0008 : Block := .branch 54 ![385, 144115188075857410, 9223372036854781956, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 48).pointIds 48), (.leaf 1 (Common.fact 49).pointIds 49), B0009, (.leaf 3 (Common.fact 50).pointIds 50), (.leaf 4 (Common.fact 51).pointIds 51), (.leaf 5 (Common.fact 52).pointIds 52), (.leaf 6 (Common.fact 53).pointIds 53)]
theorem treeEq0008 : B0008.tree = HexagonCover.NBand.M7700_7900.SplitData.node0008 := by
  change Tree.branch (54 : Fin 172) _ = Tree.branch (54 : Fin 172) _
  apply congrArg (Tree.branch (54 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0009
  · rfl
  · rfl
  · rfl
  · rfl

def B0007 : Block := .branch 57 ![385, 1538, 9223372036854781956, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 42).pointIds 42), B0008, (.leaf 2 (Common.fact 43).pointIds 43), (.leaf 3 (Common.fact 44).pointIds 44), (.leaf 4 (Common.fact 45).pointIds 45), (.leaf 5 (Common.fact 46).pointIds 46), (.leaf 6 (Common.fact 47).pointIds 47)]
theorem treeEq0007 : B0007.tree = HexagonCover.NBand.M7700_7900.SplitData.node0007 := by
  change Tree.branch (57 : Fin 172) _ = Tree.branch (57 : Fin 172) _
  apply congrArg (Tree.branch (57 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0008
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0006 : Block := .branch 48 ![385, 1538, 9223372036854781956, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 36).pointIds 36), B0007, (.leaf 2 (Common.fact 37).pointIds 37), (.leaf 3 (Common.fact 38).pointIds 38), (.leaf 4 (Common.fact 39).pointIds 39), (.leaf 5 (Common.fact 40).pointIds 40), (.leaf 6 (Common.fact 41).pointIds 41)]
theorem treeEq0006 : B0006.tree = HexagonCover.NBand.M7700_7900.SplitData.node0006 := by
  change Tree.branch (48 : Fin 172) _ = Tree.branch (48 : Fin 172) _
  apply congrArg (Tree.branch (48 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0007
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0005 : Block := .branch 63 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 30).pointIds 30), (.leaf 1 (Common.fact 31).pointIds 31), B0006, (.leaf 3 (Common.fact 32).pointIds 32), (.leaf 4 (Common.fact 33).pointIds 33), (.leaf 5 (Common.fact 34).pointIds 34), (.leaf 6 (Common.fact 35).pointIds 35)]
theorem treeEq0005 : B0005.tree = HexagonCover.NBand.M7700_7900.SplitData.node0005 := by
  change Tree.branch (63 : Fin 172) _ = Tree.branch (63 : Fin 172) _
  apply congrArg (Tree.branch (63 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0006
  · rfl
  · rfl
  · rfl
  · rfl

def B0004 : Block := .branch 62 ![385, 1538, 6148, 81129638414606681695789005168648, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 24).pointIds 24), (.leaf 1 (Common.fact 25).pointIds 25), B0005, (.leaf 3 (Common.fact 26).pointIds 26), (.leaf 4 (Common.fact 27).pointIds 27), (.leaf 5 (Common.fact 28).pointIds 28), (.leaf 6 (Common.fact 29).pointIds 29)]
theorem treeEq0004 : B0004.tree = HexagonCover.NBand.M7700_7900.SplitData.node0004 := by
  change Tree.branch (62 : Fin 172) _ = Tree.branch (62 : Fin 172) _
  apply congrArg (Tree.branch (62 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0005
  · rfl
  · rfl
  · rfl
  · rfl

def B0003 : Block := .branch 106 ![385, 1538, 6148, 24584, 98320, 393248, 21778071482940061661655974876182920822848] ![(.leaf 0 (Common.fact 18).pointIds 18), (.leaf 1 (Common.fact 19).pointIds 19), (.leaf 2 (Common.fact 20).pointIds 20), B0004, (.leaf 4 (Common.fact 21).pointIds 21), (.leaf 5 (Common.fact 22).pointIds 22), (.leaf 6 (Common.fact 23).pointIds 23)]
theorem treeEq0003 : B0003.tree = HexagonCover.NBand.M7700_7900.SplitData.node0003 := by
  change Tree.branch (106 : Fin 172) _ = Tree.branch (106 : Fin 172) _
  apply congrArg (Tree.branch (106 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0004
  · rfl
  · rfl
  · rfl

def B0002 : Block := .branch 134 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 12).pointIds 12), (.leaf 1 (Common.fact 13).pointIds 13), (.leaf 2 (Common.fact 14).pointIds 14), (.leaf 3 (Common.fact 15).pointIds 15), (.leaf 4 (Common.fact 16).pointIds 16), (.leaf 5 (Common.fact 17).pointIds 17), B0003]
theorem treeEq0002 : B0002.tree = HexagonCover.NBand.M7700_7900.SplitData.node0002 := by
  change Tree.branch (134 : Fin 172) _ = Tree.branch (134 : Fin 172) _
  apply congrArg (Tree.branch (134 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0003

def B0001 : Block := .branch 45 ![385, 1538, 6148, 24584, 98320, 393248, 1298074214633706907133173837594688] ![(.leaf 0 (Common.fact 6).pointIds 6), (.leaf 1 (Common.fact 7).pointIds 7), B0002, (.leaf 3 (Common.fact 8).pointIds 8), (.leaf 4 (Common.fact 9).pointIds 9), (.leaf 5 (Common.fact 10).pointIds 10), (.leaf 6 (Common.fact 11).pointIds 11)]
theorem treeEq0001 : B0001.tree = HexagonCover.NBand.M7700_7900.SplitData.node0001 := by
  change Tree.branch (45 : Fin 172) _ = Tree.branch (45 : Fin 172) _
  apply congrArg (Tree.branch (45 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0002
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0001 : B0001.accepted = true := by decide +kernel
theorem checked0001 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0001 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 1298074214633706907133173837594688]) := by
  rw [← treeEq0001]
  exact B0001.sound accepted0001
#print axioms checked0001

def Tip0000_0001 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0001 ![385, 1538, 6148, 24584, 98320, 393248, 1298074214633706907133173837594688] checked0001
def B0000 : Block := .branch 110 ![385, 1538, 6148, 24584, 98320, 393248, 549755289664] ![(.leaf 0 (Common.fact 0).pointIds 0), (.leaf 1 (Common.fact 1).pointIds 1), (.leaf 2 (Common.fact 2).pointIds 2), (.leaf 3 (Common.fact 3).pointIds 3), (.leaf 4 (Common.fact 4).pointIds 4), (.leaf 5 (Common.fact 5).pointIds 5), Tip0000_0001]
theorem treeEq0000 : B0000.tree = HexagonCover.NBand.M7700_7900.SplitData.node0000 := by
  change Tree.branch (110 : Fin 172) _ = Tree.branch (110 : Fin 172) _
  apply congrArg (Tree.branch (110 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0000 : B0000.accepted = true := by decide +kernel
theorem checked0000 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0000 (maskNeeds ![385, 1538, 6148, 24584, 98320, 393248, 549755289664]) := by
  rw [← treeEq0000]
  exact B0000.sound accepted0000
#print axioms checked0000

end HexagonCover.NBand.M7700_7900.SplitTree.Run0009
