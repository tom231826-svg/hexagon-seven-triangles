import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0007
import HexagonCover.NBand.M8300_8500.SplitTree.Run0008
import HexagonCover.NBand.M8300_8500.SplitTree.Run0009
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0010
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0589_0591 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0591 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0008.checked0591
def B0696 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0696 : B0696.tree = HexagonCover.NBand.M8300_8500.SplitData.node0696 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0695 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0696, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0695 : B0695.tree = HexagonCover.NBand.M8300_8500.SplitData.node0695 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0696
  · rfl

def B0694 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B0695]
theorem treeEq0694 : B0694.tree = HexagonCover.NBand.M8300_8500.SplitData.node0694 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0695

def B0693 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B0694, (.leaf 0 [] 0)]
theorem treeEq0693 : B0693.tree = HexagonCover.NBand.M8300_8500.SplitData.node0693 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0694
  · rfl

def B0692 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B0693, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0692 : B0692.tree = HexagonCover.NBand.M8300_8500.SplitData.node0692 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0693
  · rfl

def B0590 : Block := .branch 98 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0589_0591, B0692, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0590 : B0590.tree = HexagonCover.NBand.M8300_8500.SplitData.node0590 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0692
  · rfl
  · rfl

def B0699 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0699 : B0699.tree = HexagonCover.NBand.M8300_8500.SplitData.node0699 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0698 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0699, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0698 : B0698.tree = HexagonCover.NBand.M8300_8500.SplitData.node0698 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0699
  · rfl

def B0697 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158533696280984011454269120520, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), B0698]
theorem treeEq0697 : B0697.tree = HexagonCover.NBand.M8300_8500.SplitData.node0697 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0698

def B0589 : Block := .branch 86 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0590, B0697, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0589 : B0589.tree = HexagonCover.NBand.M8300_8500.SplitData.node0589 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0590
  · exact treeEq0697
  · rfl
  · rfl
  · rfl

theorem accepted0589 : B0589.accepted = true := by decide +kernel
theorem checked0589 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0589 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0589]
  exact B0589.sound accepted0589
#print axioms checked0589

def Tip0588_0702 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0702 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0009.checked0702
def Tip0588_0589 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0589 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0589
def B0807 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0807 : B0807.tree = HexagonCover.NBand.M8300_8500.SplitData.node0807 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0806 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0807, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0806 : B0806.tree = HexagonCover.NBand.M8300_8500.SplitData.node0806 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0807
  · rfl

def B0805 : Block := .branch 163 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B0806]
theorem treeEq0805 : B0805.tree = HexagonCover.NBand.M8300_8500.SplitData.node0805 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0806

def B0804 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B0805, (.leaf 0 [] 0)]
theorem treeEq0804 : B0804.tree = HexagonCover.NBand.M8300_8500.SplitData.node0804 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0805
  · rfl

def B0803 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649354019966910510916686217052176, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B0804, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0803 : B0803.tree = HexagonCover.NBand.M8300_8500.SplitData.node0803 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0804
  · rfl

def B0701 : Block := .branch 98 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), Tip0588_0702, B0803, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq0701 : B0701.tree = HexagonCover.NBand.M8300_8500.SplitData.node0701 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0803
  · rfl
  · rfl

def B0810 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0810 : B0810.tree = HexagonCover.NBand.M8300_8500.SplitData.node0810 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0809 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0810, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0809 : B0809.tree = HexagonCover.NBand.M8300_8500.SplitData.node0809 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0810
  · rfl

def B0808 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158533696280984011454269120520, 649037107316853453566312041250832, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), B0809]
theorem treeEq0808 : B0808.tree = HexagonCover.NBand.M8300_8500.SplitData.node0808 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0809

def B0700 : Block := .branch 86 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0701, B0808, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0700 : B0700.tree = HexagonCover.NBand.M8300_8500.SplitData.node0700 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0701
  · exact treeEq0808
  · rfl
  · rfl
  · rfl

def B0588 : Block := .branch 78 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0588_0589, B0700, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 232).pointIds 232)]
theorem treeEq0588 : B0588.tree = HexagonCover.NBand.M8300_8500.SplitData.node0588 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0700
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0588 : B0588.accepted = true := by decide +kernel
theorem checked0588 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0588 (maskNeeds ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq0588]
  exact B0588.sound accepted0588
#print axioms checked0588

def Tip0041_0516 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0516 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582572261937474045661797649400596738342976] HexagonCover.NBand.M8300_8500.SplitTree.Run0007.checked0516
def Tip0041_0042 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0042 ![1267650600523956019228173140353, 226673591178292726072834, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] HexagonCover.NBand.M8300_8500.SplitTree.Run0007.checked0042
def B0584 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0584 : B0584.tree = HexagonCover.NBand.M8300_8500.SplitData.node0584 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0583 : Block := .branch 169 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 674).pointIds 674), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 683).pointIds 683), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0584, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0583 : B0583.tree = HexagonCover.NBand.M8300_8500.SplitData.node0583 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0584
  · rfl

def B0582 : Block := .branch 86 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0583, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0582 : B0582.tree = HexagonCover.NBand.M8300_8500.SplitData.node0582 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0583
  · rfl
  · rfl
  · rfl
  · rfl

def B0581 : Block := .branch 138 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0582, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0581 : B0581.tree = HexagonCover.NBand.M8300_8500.SplitData.node0581 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0582
  · rfl
  · rfl

def B0580 : Block := .branch 165 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 89202980794771529673459726544159758065172496, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0581, (.leaf 0 [] 0)]
theorem treeEq0580 : B0580.tree = HexagonCover.NBand.M8300_8500.SplitData.node0580 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0581
  · rfl

def B0579 : Block := .branch 167 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 89202980794771529673459726544159758065172496, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0580, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0579 : B0579.tree = HexagonCover.NBand.M8300_8500.SplitData.node0579 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0580
  · rfl

def B0578 : Block := .branch 146 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0579, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0578 : B0578.tree = HexagonCover.NBand.M8300_8500.SplitData.node0578 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0579
  · rfl
  · rfl

def B0577 : Block := .branch 161 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B0578]
theorem treeEq0577 : B0577.tree = HexagonCover.NBand.M8300_8500.SplitData.node0577 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0578

def B0576 : Block := .branch 170 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 676).pointIds 676), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 685).pointIds 685), B0577, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0576 : B0576.tree = HexagonCover.NBand.M8300_8500.SplitData.node0576 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0577
  · rfl
  · rfl
  · rfl

def B0575 : Block := .branch 160 ![1267650600523956019228173140353, 453384075844183115433474, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 689).pointIds 689), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B0576]
theorem treeEq0575 : B0575.tree = HexagonCover.NBand.M8300_8500.SplitData.node0575 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0576

def B0515 : Block := .branch 78 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip0041_0516, B0575, (.leaf 2 (Common.fact 228).pointIds 228), (.leaf 3 (Common.fact 229).pointIds 229), (.leaf 4 (Common.fact 230).pointIds 230), (.leaf 5 (Common.fact 231).pointIds 231), (.leaf 6 (Common.fact 232).pointIds 232)]
theorem treeEq0515 : B0515.tree = HexagonCover.NBand.M8300_8500.SplitData.node0515 := by
  change Tree.branch (78 : Fin 177) _ = Tree.branch (78 : Fin 177) _
  apply congrArg (Tree.branch (78 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0575
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0514 : Block := .branch 171 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 672).pointIds 672), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 681).pointIds 681), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 563).pointIds 563), B0515]
theorem treeEq0514 : B0514.tree = HexagonCover.NBand.M8300_8500.SplitData.node0514 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0515

def B0513 : Block := .branch 168 ![1267650600523956019228173140353, 151152620940525821756930, 53268293926769598010497028, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 670).pointIds 670), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 679).pointIds 679), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 561).pointIds 561), B0514]
theorem treeEq0513 : B0513.tree = HexagonCover.NBand.M8300_8500.SplitData.node0513 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0514

def B0041 : Block := .branch 76 ![1267650600523956019228173140353, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip0041_0042, B0513, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 227).pointIds 227)]
theorem treeEq0041 : B0041.tree = HexagonCover.NBand.M8300_8500.SplitData.node0041 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0513
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0041 : B0041.accepted = true := by decide +kernel
theorem checked0041 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0041 (maskNeeds ![1267650600523956019228173140353, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576]) := by
  rw [← treeEq0041]
  exact B0041.sound accepted0041
#print axioms checked0041

def Tip0039_0588 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0588 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] checked0588
def Tip0039_0041 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0041 ![1267650600523956019228173140353, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] checked0041
def B0820 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq0820 : B0820.tree = HexagonCover.NBand.M8300_8500.SplitData.node0820 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0819 : Block := .branch 169 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 698).pointIds 698), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 587).pointIds 587), B0820, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0819 : B0819.tree = HexagonCover.NBand.M8300_8500.SplitData.node0819 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0820
  · rfl

def B0818 : Block := .branch 86 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0819, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 615).pointIds 615)]
theorem treeEq0818 : B0818.tree = HexagonCover.NBand.M8300_8500.SplitData.node0818 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0819
  · rfl
  · rfl
  · rfl
  · rfl

def B0817 : Block := .branch 138 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0818, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M8300_8500.SplitData.node0817 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0818
  · rfl
  · rfl

def B0816 : Block := .branch 165 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626844588240731725026502340802862011932680, 89202980794771529673459726544159758065172496, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B0817, (.leaf 0 [] 0)]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M8300_8500.SplitData.node0816 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0817
  · rfl

def B0815 : Block := .branch 167 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626844588240731725026502340802862011932680, 89202980794771529673459726544159758065172496, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B0816, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M8300_8500.SplitData.node0815 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0816
  · rfl

def B0814 : Block := .branch 146 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0815, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M8300_8500.SplitData.node0814 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0815
  · rfl
  · rfl

def B0813 : Block := .branch 161 ![1267650600228808114048820314497, 151447768845705174582786, 53306072858632555172206596, 1496577676626844588240731725026502340802862011932680, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B0814]
theorem treeEq0813 : B0813.tree = HexagonCover.NBand.M8300_8500.SplitData.node0813 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0814

def B0812 : Block := .branch 170 ![1267650600228808114048820314497, 151447768845705174582786, 53306072858632555172206596, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 699).pointIds 699), (.leaf 1 (Common.fact 700).pointIds 700), (.leaf 2 (Common.fact 430).pointIds 430), B0813, (.leaf 4 (Common.fact 590).pointIds 590), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M8300_8500.SplitData.node0812 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0813
  · rfl
  · rfl
  · rfl

def B0811 : Block := .branch 160 ![1267650600228808114048820314497, 151447768845705174582786, 53306072858632555172206596, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 701).pointIds 701), (.leaf 2 (Common.fact 690).pointIds 690), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B0812]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M8300_8500.SplitData.node0811 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0812

def B0587 : Block := .branch 76 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 223).pointIds 223), Tip0039_0588, B0811, (.leaf 3 (Common.fact 224).pointIds 224), (.leaf 4 (Common.fact 225).pointIds 225), (.leaf 5 (Common.fact 226).pointIds 226), (.leaf 6 (Common.fact 227).pointIds 227)]
theorem treeEq0587 : B0587.tree = HexagonCover.NBand.M8300_8500.SplitData.node0587 := by
  change Tree.branch (76 : Fin 177) _ = Tree.branch (76 : Fin 177) _
  apply congrArg (Tree.branch (76 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0811
  · rfl
  · rfl
  · rfl
  · rfl

def B0586 : Block := .branch 171 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 695).pointIds 695), (.leaf 1 (Common.fact 696).pointIds 696), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 595).pointIds 595), (.leaf 5 (Common.fact 563).pointIds 563), B0587]
theorem treeEq0586 : B0586.tree = HexagonCover.NBand.M8300_8500.SplitData.node0586 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0587

def B0585 : Block := .branch 168 ![1267650600228808114048820314497, 151447768845705174582786, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![(.leaf 0 (Common.fact 693).pointIds 693), (.leaf 1 (Common.fact 694).pointIds 694), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 586).pointIds 586), (.leaf 5 (Common.fact 561).pointIds 561), B0586]
theorem treeEq0585 : B0585.tree = HexagonCover.NBand.M8300_8500.SplitData.node0585 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0586

def B0040 : Block := .branch 68 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 11172177255308167330746973187341569280704576] ![Tip0039_0041, B0585, (.leaf 2 (Common.fact 218).pointIds 218), (.leaf 3 (Common.fact 219).pointIds 219), (.leaf 4 (Common.fact 220).pointIds 220), (.leaf 5 (Common.fact 221).pointIds 221), (.leaf 6 (Common.fact 222).pointIds 222)]
theorem treeEq0040 : B0040.tree = HexagonCover.NBand.M8300_8500.SplitData.node0040 := by
  change Tree.branch (68 : Fin 177) _ = Tree.branch (68 : Fin 177) _
  apply congrArg (Tree.branch (68 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0585
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0039 : Block := .branch 143 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 216).pointIds 216), (.leaf 5 (Common.fact 217).pointIds 217), B0040]
theorem treeEq0039 : B0039.tree = HexagonCover.NBand.M8300_8500.SplitData.node0039 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0040

theorem accepted0039 : B0039.accepted = true := by decide +kernel
theorem checked0039 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0039 (maskNeeds ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0039]
  exact B0039.sound accepted0039
#print axioms checked0039

def B0847 : Block := .branch 132 ![385, 1538, 6148, 24584, 11692102650077161195163031391098952760824132894736, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), (.leaf 4 (Common.fact 664).pointIds 664), (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 762).pointIds 762)]
theorem treeEq0847 : B0847.tree = HexagonCover.NBand.M8300_8500.SplitData.node0847 := by
  change Tree.branch (132 : Fin 177) _ = Tree.branch (132 : Fin 177) _
  apply congrArg (Tree.branch (132 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0846 : Block := .branch 163 ![385, 1538, 6148, 24584, 89551429937849533552729368688603576672550928, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0847, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq0846 : B0846.tree = HexagonCover.NBand.M8300_8500.SplitData.node0846 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0847
  · rfl
  · rfl

def B0845 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202980794122492566142873090593446024019984, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B0846, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq0845 : B0845.tree = HexagonCover.NBand.M8300_8500.SplitData.node0845 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0846
  · rfl
  · rfl

def B0844 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202982123350488351058745994400506304364560, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 760).pointIds 760), B0845, (.leaf 0 [] 0)]
theorem treeEq0844 : B0844.tree = HexagonCover.NBand.M8300_8500.SplitData.node0844 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0845
  · rfl

def B0843 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 89202982123350488351058745994400506304364560, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 759).pointIds 759), B0844, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0843 : B0843.tree = HexagonCover.NBand.M8300_8500.SplitData.node0843 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0844
  · rfl

def B0842 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573268701473812127674924032008, 1329227995784915872903807060280442896, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B0843, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq0842 : B0842.tree = HexagonCover.NBand.M8300_8500.SplitData.node0842 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0843
  · rfl
  · rfl

def B0841 : Block := .branch 88 ![385, 1538, 2923003274661805836407374501135844497828563916804, 1496577676626844588240573268701473812127674924032008, 1329227995784915872903807060280442896, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 577).pointIds 577), B0842, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 758).pointIds 758)]
theorem treeEq0841 : B0841.tree = HexagonCover.NBand.M8300_8500.SplitData.node0841 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0842
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0840 : Block := .branch 161 ![385, 1538, 4835703278458516698830852, 1496577676626844588240573268701473812127674924032008, 1329227995784915872903807060280442896, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0841, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq0840 : B0840.tree = HexagonCover.NBand.M8300_8500.SplitData.node0840 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0841
  · rfl
  · rfl
  · rfl
  · rfl

def B0839 : Block := .branch 170 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 24584, 1329227995784915872903807060280442896, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 754).pointIds 754), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 430).pointIds 430), B0840, (.leaf 4 (Common.fact 755).pointIds 755), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq0839 : B0839.tree = HexagonCover.NBand.M8300_8500.SplitData.node0839 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0840
  · rfl
  · rfl
  · rfl

def B0838 : Block := .branch 169 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 752).pointIds 752), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 753).pointIds 753), (.leaf 5 (Common.fact 589).pointIds 589), B0839]
theorem treeEq0838 : B0838.tree = HexagonCover.NBand.M8300_8500.SplitData.node0838 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0839

def B0837 : Block := .branch 135 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B0838, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq0837 : B0837.tree = HexagonCover.NBand.M8300_8500.SplitData.node0837 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0838
  · rfl

def B0836 : Block := .branch 171 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 374144430328888402369578298522569869774984714911808] ![(.leaf 0 (Common.fact 749).pointIds 749), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 750).pointIds 750), (.leaf 5 (Common.fact 563).pointIds 563), B0837]
theorem treeEq0836 : B0836.tree = HexagonCover.NBand.M8300_8500.SplitData.node0836 := by
  change Tree.branch (171 : Fin 177) _ = Tree.branch (171 : Fin 177) _
  apply congrArg (Tree.branch (171 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0837

def B0835 : Block := .branch 168 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 1329227995784915872903807060280442896, 393248, 11172177255309434981347201416743065983909952] ![(.leaf 0 (Common.fact 747).pointIds 747), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 748).pointIds 748), (.leaf 5 (Common.fact 561).pointIds 561), B0836]
theorem treeEq0835 : B0835.tree = HexagonCover.NBand.M8300_8500.SplitData.node0835 := by
  change Tree.branch (168 : Fin 177) _ = Tree.branch (168 : Fin 177) _
  apply congrArg (Tree.branch (168 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0836

def B0834 : Block := .branch 120 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 98320, 393248, 11172177255309434981347201416743065983909952] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0835, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 746).pointIds 746)]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M8300_8500.SplitData.node0834 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0835
  · rfl
  · rfl

def B0833 : Block := .branch 130 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 11172177255309434981347201416743065983909952] ![(.leaf 0 (Common.fact 735).pointIds 735), (.leaf 1 (Common.fact 736).pointIds 736), (.leaf 2 (Common.fact 737).pointIds 737), (.leaf 3 (Common.fact 738).pointIds 738), B0834, (.leaf 5 (Common.fact 739).pointIds 739), (.leaf 6 (Common.fact 740).pointIds 740)]
theorem treeEq0833 : B0833.tree = HexagonCover.NBand.M8300_8500.SplitData.node0833 := by
  change Tree.branch (130 : Fin 177) _ = Tree.branch (130 : Fin 177) _
  apply congrArg (Tree.branch (130 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0834
  · rfl
  · rfl

def B0832 : Block := .branch 131 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 11172177255309434981347201416743065983909952] ![(.leaf 0 (Common.fact 729).pointIds 729), (.leaf 1 (Common.fact 730).pointIds 730), (.leaf 2 (Common.fact 731).pointIds 731), (.leaf 3 (Common.fact 732).pointIds 732), B0833, (.leaf 5 (Common.fact 733).pointIds 733), (.leaf 6 (Common.fact 734).pointIds 734)]
theorem treeEq0832 : B0832.tree = HexagonCover.NBand.M8300_8500.SplitData.node0832 := by
  change Tree.branch (131 : Fin 177) _ = Tree.branch (131 : Fin 177) _
  apply congrArg (Tree.branch (131 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0833
  · rfl
  · rfl

def B0831 : Block := .branch 140 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 11172177255309434981347201416743065983909952] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B0832, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 728).pointIds 728)]
theorem treeEq0831 : B0831.tree = HexagonCover.NBand.M8300_8500.SplitData.node0831 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0832
  · rfl
  · rfl

def B0830 : Block := .branch 143 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 696898287454081973172991196020261297160208, 393248, 21804656044123410579342280418885230919744] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 727).pointIds 727), (.leaf 5 (Common.fact 217).pointIds 217), B0831]
theorem treeEq0830 : B0830.tree = HexagonCover.NBand.M8300_8500.SplitData.node0830 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0831

def B0829 : Block := .branch 139 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 21804656044123410579342280418885230919744] ![(.leaf 0 (Common.fact 721).pointIds 721), (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), B0830, (.leaf 5 (Common.fact 725).pointIds 725), (.leaf 6 (Common.fact 726).pointIds 726)]
theorem treeEq0829 : B0829.tree = HexagonCover.NBand.M8300_8500.SplitData.node0829 := by
  change Tree.branch (139 : Fin 177) _ = Tree.branch (139 : Fin 177) _
  apply congrArg (Tree.branch (139 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0830
  · rfl
  · rfl

def B0828 : Block := .branch 148 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 21804656044123410579342280418885230919744] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B0829, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 720).pointIds 720)]
theorem treeEq0828 : B0828.tree = HexagonCover.NBand.M8300_8500.SplitData.node0828 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0829
  · rfl
  · rfl

theorem accepted0828 : B0828.accepted = true := by decide +kernel
theorem checked0828 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0828 (maskNeeds ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 21804656044123410579342280418885230919744]) := by
  rw [← treeEq0828]
  exact B0828.sound accepted0828
#print axioms checked0828

end HexagonCover.NBand.M8300_8500.SplitTree.Run0010
