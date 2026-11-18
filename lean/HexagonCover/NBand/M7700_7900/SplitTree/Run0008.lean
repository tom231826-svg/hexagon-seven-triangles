import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.NBand.M7700_7900.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def Tip0586_0588 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0588 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7700_7900.SplitTree.Run0007.checked0588
def B0635 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 1511192693021931688905867091340349674550791346061376] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 821).pointIds 821), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0635 : B0635.tree = HexagonCover.NBand.M7700_7900.SplitData.node0635 := by
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

def B0634 : Block := .branch 170 ![748288838313422294120286634350736906063837462004097, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 820).pointIds 820), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0635]
theorem treeEq0634 : B0634.tree = HexagonCover.NBand.M7700_7900.SplitData.node0634 := by
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
  · exact treeEq0635

def B0633 : Block := .branch 169 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0634, (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0633 : B0633.tree = HexagonCover.NBand.M7700_7900.SplitData.node0633 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0634
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0632 : Block := .branch 163 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0633]
theorem treeEq0632 : B0632.tree = HexagonCover.NBand.M7700_7900.SplitData.node0632 := by
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
  · exact treeEq0633

def B0631 : Block := .branch 165 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0632, (.leaf 0 [] 0)]
theorem treeEq0631 : B0631.tree = HexagonCover.NBand.M7700_7900.SplitData.node0631 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0632
  · rfl

def B0630 : Block := .branch 167 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0631, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0630 : B0630.tree = HexagonCover.NBand.M7700_7900.SplitData.node0630 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0631
  · rfl

def B0629 : Block := .branch 143 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0630, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0629 : B0629.tree = HexagonCover.NBand.M7700_7900.SplitData.node0629 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0630
  · rfl
  · rfl

def B0628 : Block := .branch 144 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0629, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0628 : B0628.tree = HexagonCover.NBand.M7700_7900.SplitData.node0628 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0629
  · rfl

def B0627 : Block := .branch 161 ![385, 216172782113785346, 9223512774343137284, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 779).pointIds 779), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0628]
theorem treeEq0627 : B0627.tree = HexagonCover.NBand.M7700_7900.SplitData.node0627 := by
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
  · exact treeEq0628

def B0587 : Block := .branch 72 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), Tip0586_0588, B0627, (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M7700_7900.SplitData.node0587 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0627
  · rfl
  · rfl
  · rfl

def B0644 : Block := .branch 108 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 1511192693021931688905867091340349674550791346061376] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), (.leaf 4 (Common.fact 821).pointIds 821), (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0644 : B0644.tree = HexagonCover.NBand.M7700_7900.SplitData.node0644 := by
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

def B0643 : Block := .branch 170 ![748288838313422294120286634350736906063837462004097, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![(.leaf 0 (Common.fact 820).pointIds 820), (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), B0644]
theorem treeEq0643 : B0643.tree = HexagonCover.NBand.M7700_7900.SplitData.node0643 := by
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
  · exact treeEq0644

def B0642 : Block := .branch 169 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0643, (.leaf 1 (Common.fact 818).pointIds 818), (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0642 : B0642.tree = HexagonCover.NBand.M7700_7900.SplitData.node0642 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0643
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0641 : Block := .branch 163 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0642]
theorem treeEq0641 : B0641.tree = HexagonCover.NBand.M7700_7900.SplitData.node0641 := by
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
  · exact treeEq0642

def B0640 : Block := .branch 165 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0641, (.leaf 0 [] 0)]
theorem treeEq0640 : B0640.tree = HexagonCover.NBand.M7700_7900.SplitData.node0640 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0641
  · rfl

def B0639 : Block := .branch 167 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0640, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0639 : B0639.tree = HexagonCover.NBand.M7700_7900.SplitData.node0639 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0640
  · rfl

def B0638 : Block := .branch 143 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0639, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0638 : B0638.tree = HexagonCover.NBand.M7700_7900.SplitData.node0638 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0639
  · rfl
  · rfl

def B0637 : Block := .branch 144 ![385, 216172782113785346, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0638, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0637 : B0637.tree = HexagonCover.NBand.M7700_7900.SplitData.node0637 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0638
  · rfl

def B0636 : Block := .branch 161 ![385, 216172782113785346, 9223512774343137284, 38687987410909568413229064, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 781).pointIds 781), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0637]
theorem treeEq0636 : B0636.tree = HexagonCover.NBand.M7700_7900.SplitData.node0636 := by
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
  · exact treeEq0637

def B0586 : Block := .branch 71 ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0587, B0636, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M7700_7900.SplitData.node0586 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0587
  · exact treeEq0636
  · rfl
  · rfl
  · rfl

theorem accepted0586 : B0586.accepted = true := by decide +kernel
theorem checked0586 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0586 (maskNeeds ![590295810358705652097, 216172782113785346, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0586]
  exact B0586.sound accepted0586
#print axioms checked0586

def B0682 : Block := .branch 160 ![385, 748288838313422294120286634652968360967494755681794, 9223512774343137284, 24584, 98320, 393248, 2993155353280911765835138991357589382218418323193920] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 832).pointIds 832), (.leaf 2 (Common.fact 792).pointIds 792), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M7700_7900.SplitData.node0682 := by
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
  · rfl

def B0681 : Block := .branch 169 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353280911765835138991357589382218418323193920] ![(.leaf 0 (Common.fact 820).pointIds 820), B0682, (.leaf 2 (Common.fact 819).pointIds 819), (.leaf 3 (Common.fact 484).pointIds 484), (.leaf 4 (Common.fact 696).pointIds 696), (.leaf 5 (Common.fact 697).pointIds 697), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M7700_7900.SplitData.node0681 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0682
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0680 : Block := .branch 132 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 184118785299649822107371341510562984030508253200, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 694).pointIds 694), (.leaf 5 (Common.fact 207).pointIds 207), B0681]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M7700_7900.SplitData.node0680 := by
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
  · exact treeEq0681

def B0679 : Block := .branch 157 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 5709034326966805404356467189747731811862446112, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), (.leaf 3 (Common.fact 200).pointIds 200), B0680, (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 0 [] 0)]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M7700_7900.SplitData.node0679 := by
  change Tree.branch (157 : Fin 172) _ = Tree.branch (157 : Fin 172) _
  apply congrArg (Tree.branch (157 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0680
  · rfl
  · rfl

def B0678 : Block := .branch 135 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 191).pointIds 191), (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), B0679, (.leaf 6 (Common.fact 813).pointIds 813)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M7700_7900.SplitData.node0678 := by
  change Tree.branch (135 : Fin 172) _ = Tree.branch (135 : Fin 172) _
  apply congrArg (Tree.branch (135 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl

def B0677 : Block := .branch 76 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 5708990770823839524233143877797980545531379744, 2993155353286356283705874006773003375937326614577216] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 830).pointIds 830), B0678, (.leaf 3 (Common.fact 324).pointIds 324), (.leaf 4 (Common.fact 325).pointIds 325), (.leaf 5 (Common.fact 326).pointIds 326), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M7700_7900.SplitData.node0677 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0678
  · rfl
  · rfl
  · rfl
  · rfl

def B0676 : Block := .branch 133 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 38685626227668133590622216, 1431080633286957331910737421027606573516685328, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 161).pointIds 161), (.leaf 1 (Common.fact 162).pointIds 162), (.leaf 2 (Common.fact 163).pointIds 163), (.leaf 3 (Common.fact 164).pointIds 164), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 166).pointIds 166), B0677]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M7700_7900.SplitData.node0676 := by
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
  · exact treeEq0677

def B0675 : Block := .branch 138 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 1430732184143230290924150925429596442868154384, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 155).pointIds 155), (.leaf 1 (Common.fact 156).pointIds 156), (.leaf 2 (Common.fact 157).pointIds 157), (.leaf 3 (Common.fact 158).pointIds 158), B0676, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0675 : B0675.tree = HexagonCover.NBand.M7700_7900.SplitData.node0675 := by
  change Tree.branch (138 : Fin 172) _ = Tree.branch (138 : Fin 172) _
  apply congrArg (Tree.branch (138 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0676
  · rfl
  · rfl

def B0674 : Block := .branch 139 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 686).pointIds 686), (.leaf 1 (Common.fact 687).pointIds 687), (.leaf 2 (Common.fact 688).pointIds 688), (.leaf 3 (Common.fact 689).pointIds 689), B0675, (.leaf 5 (Common.fact 690).pointIds 690), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0674 : B0674.tree = HexagonCover.NBand.M7700_7900.SplitData.node0674 := by
  change Tree.branch (139 : Fin 172) _ = Tree.branch (139 : Fin 172) _
  apply congrArg (Tree.branch (139 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0675
  · rfl
  · rfl

def B0673 : Block := .branch 140 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 1430035285855776208950977934233576181571092496, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 185).pointIds 185), (.leaf 1 (Common.fact 186).pointIds 186), (.leaf 2 (Common.fact 187).pointIds 187), (.leaf 3 (Common.fact 188).pointIds 188), B0674, (.leaf 5 (Common.fact 189).pointIds 189), (.leaf 6 (Common.fact 808).pointIds 808)]
theorem treeEq0673 : B0673.tree = HexagonCover.NBand.M7700_7900.SplitData.node0673 := by
  change Tree.branch (140 : Fin 172) _ = Tree.branch (140 : Fin 172) _
  apply congrArg (Tree.branch (140 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0674
  · rfl
  · rfl

def B0672 : Block := .branch 141 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0673, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 807).pointIds 807)]
theorem treeEq0672 : B0672.tree = HexagonCover.NBand.M7700_7900.SplitData.node0672 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0673
  · rfl
  · rfl

def B0671 : Block := .branch 144 ![1496577676626844588240573268701473812127674924007809, 302231454903657293678082, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2993155353275467247964403975942175388499510031810624] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0672, (.leaf 6 (Common.fact 806).pointIds 806)]
theorem treeEq0671 : B0671.tree = HexagonCover.NBand.M7700_7900.SplitData.node0671 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0672
  · rfl

def B0670 : Block := .branch 171 ![1496577676626844588240573268701473812127674924007809, 302231599018845369533954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0671]
theorem treeEq0670 : B0670.tree = HexagonCover.NBand.M7700_7900.SplitData.node0670 := by
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
  · exact treeEq0671

def B0669 : Block := .branch 170 ![385, 302231599018845369533954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257438539227764244160183795776] ![B0670, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 646).pointIds 646)]
theorem treeEq0669 : B0669.tree = HexagonCover.NBand.M7700_7900.SplitData.node0669 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0670
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0668 : Block := .branch 88 ![385, 302231599018845369533954, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 829).pointIds 829), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0669]
theorem treeEq0668 : B0668.tree = HexagonCover.NBand.M7700_7900.SplitData.node0668 := by
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
  · exact treeEq0669

def B0686 : Block := .branch 132 ![385, 1538, 6148, 24584, 1427247694035187876843201842353302196663189520, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 202).pointIds 202), (.leaf 1 (Common.fact 203).pointIds 203), (.leaf 2 (Common.fact 204).pointIds 204), (.leaf 3 (Common.fact 205).pointIds 205), (.leaf 4 (Common.fact 653).pointIds 653), (.leaf 5 (Common.fact 207).pointIds 207), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq0686 : B0686.tree = HexagonCover.NBand.M7700_7900.SplitData.node0686 := by
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

def B0685 : Block := .branch 120 ![385, 1538, 6148, 79228162514264337593543974920, 1427247692705959881058285969449495136382844944, 393248, 2993155353275467247964403666759397022058098600706112] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0686, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 816).pointIds 816)]
theorem treeEq0685 : B0685.tree = HexagonCover.NBand.M7700_7900.SplitData.node0685 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0686
  · rfl
  · rfl

def B0684 : Block := .branch 171 ![1496577676626844588240573268701473812127674924007809, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0685]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M7700_7900.SplitData.node0684 := by
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
  · exact treeEq0685

def B0683 : Block := .branch 170 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129356449397802748752691264] ![B0684, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M7700_7900.SplitData.node0683 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0684
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0667 : Block := .branch 78 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 100).pointIds 100), B0668, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), B0683]
theorem treeEq0667 : B0667.tree = HexagonCover.NBand.M7700_7900.SplitData.node0667 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0668
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0683

theorem accepted0667 : B0667.accepted = true := by decide +kernel
theorem checked0667 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0667 (maskNeeds ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0667]
  exact B0667.sound accepted0667
#print axioms checked0667

def Tip0666_0667 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0667 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0667
def B0697 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 3013616376198099888818938186722631561406715824439360] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M7700_7900.SplitData.node0697 := by
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

def B0696 : Block := .branch 171 ![1496577676626844588243108569901930270930668330418561, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0697]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M7700_7900.SplitData.node0696 := by
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
  · exact treeEq0697

def B0695 : Block := .branch 170 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![B0696, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M7700_7900.SplitData.node0695 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0696
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0694 : Block := .branch 162 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100664976909988818805072742246252608] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 754).pointIds 754), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0695]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M7700_7900.SplitData.node0694 := by
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
  · exact treeEq0695

def B0693 : Block := .branch 101 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0694, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M7700_7900.SplitData.node0693 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0694
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0692 : Block := .branch 163 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0693]
theorem treeEq0692 : B0692.tree = HexagonCover.NBand.M7700_7900.SplitData.node0692 := by
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
  · exact treeEq0693

def B0691 : Block := .branch 165 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0692, (.leaf 0 [] 0)]
theorem treeEq0691 : B0691.tree = HexagonCover.NBand.M7700_7900.SplitData.node0691 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0692
  · rfl

def B0690 : Block := .branch 167 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0691, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0690 : B0690.tree = HexagonCover.NBand.M7700_7900.SplitData.node0690 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0691
  · rfl

def B0689 : Block := .branch 143 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0690, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0689 : B0689.tree = HexagonCover.NBand.M7700_7900.SplitData.node0689 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0690
  · rfl
  · rfl

def B0688 : Block := .branch 144 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0689, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0688 : B0688.tree = HexagonCover.NBand.M7700_7900.SplitData.node0688 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0689
  · rfl

def B0687 : Block := .branch 161 ![385, 144115188075857410, 9223512774343137284, 38704515693599612171477000, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 747).pointIds 747), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0688]
theorem treeEq0687 : B0687.tree = HexagonCover.NBand.M7700_7900.SplitData.node0687 := by
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
  · exact treeEq0688

def B0666 : Block := .branch 74 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), Tip0666_0667, B0687, (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0666 : B0666.tree = HexagonCover.NBand.M7700_7900.SplitData.node0666 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0687
  · rfl
  · rfl
  · rfl

theorem accepted0666 : B0666.accepted = true := by decide +kernel
theorem checked0666 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0666 (maskNeeds ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0666]
  exact B0666.sound accepted0666
#print axioms checked0666

def Tip0665_0666 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0666 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0666
def B0708 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 3013616376198099888818938186722631561406715824439360] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M7700_7900.SplitData.node0708 := by
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

def B0707 : Block := .branch 171 ![1496577676626844588243108569901930270930668330418561, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0708]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M7700_7900.SplitData.node0707 := by
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
  · exact treeEq0708

def B0706 : Block := .branch 170 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![B0707, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M7700_7900.SplitData.node0706 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0707
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0705 : Block := .branch 162 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100664976909988818805072742246252608] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 778).pointIds 778), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0706]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M7700_7900.SplitData.node0705 := by
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
  · exact treeEq0706

def B0704 : Block := .branch 101 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0705, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M7700_7900.SplitData.node0704 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0705
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0703 : Block := .branch 163 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0704]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M7700_7900.SplitData.node0703 := by
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
  · exact treeEq0704

def B0702 : Block := .branch 165 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0703, (.leaf 0 [] 0)]
theorem treeEq0702 : B0702.tree = HexagonCover.NBand.M7700_7900.SplitData.node0702 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0703
  · rfl

def B0701 : Block := .branch 167 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0702, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M7700_7900.SplitData.node0701 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0702
  · rfl

def B0700 : Block := .branch 143 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0701, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M7700_7900.SplitData.node0700 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0701
  · rfl
  · rfl

def B0699 : Block := .branch 144 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0700, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M7700_7900.SplitData.node0699 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0700
  · rfl

def B0698 : Block := .branch 161 ![385, 144115188075857410, 9223512774343137284, 38695070960633872881049608, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 777).pointIds 777), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0699]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M7700_7900.SplitData.node0698 := by
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
  · exact treeEq0699

def B0665 : Block := .branch 73 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), Tip0665_0666, B0698, (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0665 : B0665.tree = HexagonCover.NBand.M7700_7900.SplitData.node0665 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0698
  · rfl
  · rfl
  · rfl

theorem accepted0665 : B0665.accepted = true := by decide +kernel
theorem checked0665 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0665 (maskNeeds ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0665]
  exact B0665.sound accepted0665
#print axioms checked0665

def Tip0664_0665 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0665 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] checked0665
def B0719 : Block := .branch 119 ![385, 1538, 6148, 38685626227668133590622216, 11150372599265311570767859136324180753088528, 393248, 3013616376198099888818938186722631561406715824439360] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), (.leaf 4 (Common.fact 639).pointIds 639), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 835).pointIds 835)]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M7700_7900.SplitData.node0719 := by
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

def B0718 : Block := .branch 171 ![1496577676626844588243108569901930270930668330418561, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 798).pointIds 798), (.leaf 2 (Common.fact 799).pointIds 799), (.leaf 3 (Common.fact 800).pointIds 800), (.leaf 4 (Common.fact 801).pointIds 801), (.leaf 5 (Common.fact 802).pointIds 802), B0719]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M7700_7900.SplitData.node0718 := by
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
  · exact treeEq0719

def B0717 : Block := .branch 170 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38685626227668133590622216, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 20461022944410712337791649319683937151365976424512] ![B0718, (.leaf 1 (Common.fact 793).pointIds 793), (.leaf 2 (Common.fact 794).pointIds 794), (.leaf 3 (Common.fact 674).pointIds 674), (.leaf 4 (Common.fact 644).pointIds 644), (.leaf 5 (Common.fact 645).pointIds 645), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M7700_7900.SplitData.node0717 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0718
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0716 : Block := .branch 162 ![2535301200456458802993406411137, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100664976909988818805072742246252608] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 780).pointIds 780), (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 378).pointIds 378), B0717]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M7700_7900.SplitData.node0716 := by
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
  · exact treeEq0717

def B0715 : Block := .branch 101 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 14615016395087100665293822638875862423116422053952] ![B0716, (.leaf 1 (Common.fact 606).pointIds 606), (.leaf 2 (Common.fact 607).pointIds 607), (.leaf 3 (Common.fact 608).pointIds 608), (.leaf 4 (Common.fact 609).pointIds 609), (.leaf 5 (Common.fact 610).pointIds 610), (.leaf 6 (Common.fact 753).pointIds 753)]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M7700_7900.SplitData.node0715 := by
  change Tree.branch (101 : Fin 172) _ = Tree.branch (101 : Fin 172) _
  apply congrArg (Tree.branch (101 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0716
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0714 : Block := .branch 163 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 752).pointIds 752), (.leaf 5 (Common.fact 291).pointIds 291), B0715]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M7700_7900.SplitData.node0714 := by
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
  · exact treeEq0715

def B0713 : Block := .branch 165 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), (.leaf 4 (Common.fact 751).pointIds 751), B0714, (.leaf 0 [] 0)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M7700_7900.SplitData.node0713 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0714
  · rfl

def B0712 : Block := .branch 167 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1438398065305225192629053828585819317135835152, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 549).pointIds 549), (.leaf 1 (Common.fact 550).pointIds 550), (.leaf 2 (Common.fact 551).pointIds 551), (.leaf 3 (Common.fact 552).pointIds 552), (.leaf 4 (Common.fact 750).pointIds 750), B0713, (.leaf 6 (Common.fact 554).pointIds 554)]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M7700_7900.SplitData.node0712 := by
  change Tree.branch (167 : Fin 172) _ = Tree.branch (167 : Fin 172) _
  apply congrArg (Tree.branch (167 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0713
  · rfl

def B0711 : Block := .branch 143 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 229).pointIds 229), (.leaf 1 (Common.fact 230).pointIds 230), (.leaf 2 (Common.fact 231).pointIds 231), (.leaf 3 (Common.fact 232).pointIds 232), B0712, (.leaf 5 (Common.fact 234).pointIds 234), (.leaf 6 (Common.fact 749).pointIds 749)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M7700_7900.SplitData.node0711 := by
  change Tree.branch (143 : Fin 172) _ = Tree.branch (143 : Fin 172) _
  apply congrArg (Tree.branch (143 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0712
  · rfl
  · rfl

def B0710 : Block := .branch 144 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 2923003296439877319664343977145598265868961710144] ![(.leaf 0 (Common.fact 595).pointIds 595), (.leaf 1 (Common.fact 596).pointIds 596), (.leaf 2 (Common.fact 597).pointIds 597), (.leaf 3 (Common.fact 598).pointIds 598), (.leaf 4 (Common.fact 599).pointIds 599), B0711, (.leaf 6 (Common.fact 748).pointIds 748)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M7700_7900.SplitData.node0710 := by
  change Tree.branch (144 : Fin 172) _ = Tree.branch (144 : Fin 172) _
  apply congrArg (Tree.branch (144 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0711
  · rfl

def B0709 : Block := .branch 161 ![385, 144115188075857410, 9223512774343137284, 38690348594151003235835912, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483256974311713032226557096624192] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 779).pointIds 779), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), B0710]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M7700_7900.SplitData.node0709 := by
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
  · exact treeEq0710

def B0664 : Block := .branch 72 ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), Tip0664_0665, B0709, (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0664 : B0664.tree = HexagonCover.NBand.M7700_7900.SplitData.node0664 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0709
  · rfl
  · rfl
  · rfl

theorem accepted0664 : B0664.accepted = true := by decide +kernel
theorem checked0664 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0664 (maskNeeds ![385, 144115188075857410, 9223512774343137284, 79266848140492005727134572552, 1427247692705959881058285969449495136382844944, 5708990770823839524233143877797980545531379744, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0664]
  exact B0664.sound accepted0664
#print axioms checked0664

end HexagonCover.NBand.M7700_7900.SplitTree.Run0008
