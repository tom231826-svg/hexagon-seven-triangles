import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0008
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0009
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0806 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0806 : B0806.tree = HexagonCover.NBand.M7500_7700.SplitData.node0806 := by
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

def B0805 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0806]
theorem treeEq0805 : B0805.tree = HexagonCover.NBand.M7500_7700.SplitData.node0805 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0806

def B0804 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0805, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0804 : B0804.tree = HexagonCover.NBand.M7500_7700.SplitData.node0804 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0805
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0803 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0804, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0803 : B0803.tree = HexagonCover.NBand.M7500_7700.SplitData.node0803 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0804
  · rfl

def B0802 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0803, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0802 : B0802.tree = HexagonCover.NBand.M7500_7700.SplitData.node0802 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0803
  · rfl
  · rfl

def B0801 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0802]
theorem treeEq0801 : B0801.tree = HexagonCover.NBand.M7500_7700.SplitData.node0801 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0802

def B0811 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0811 : B0811.tree = HexagonCover.NBand.M7500_7700.SplitData.node0811 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0810 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0811, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0810 : B0810.tree = HexagonCover.NBand.M7500_7700.SplitData.node0810 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0811
  · rfl

def B0809 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0810, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0809 : B0809.tree = HexagonCover.NBand.M7500_7700.SplitData.node0809 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0810
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0808 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0809, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0808 : B0808.tree = HexagonCover.NBand.M7500_7700.SplitData.node0808 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0809
  · rfl

def B0807 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 38690348594151003235835912, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 856).pointIds 856), B0808, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0807 : B0807.tree = HexagonCover.NBand.M7500_7700.SplitData.node0807 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0808
  · rfl
  · rfl

def B0800 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0801, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0807]
theorem treeEq0800 : B0800.tree = HexagonCover.NBand.M7500_7700.SplitData.node0800 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0801
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0807

def B0816 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0816 : B0816.tree = HexagonCover.NBand.M7500_7700.SplitData.node0816 := by
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

def B0815 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0816]
theorem treeEq0815 : B0815.tree = HexagonCover.NBand.M7500_7700.SplitData.node0815 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0816

def B0814 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0815, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0814 : B0814.tree = HexagonCover.NBand.M7500_7700.SplitData.node0814 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0815
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0813 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0814, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0813 : B0813.tree = HexagonCover.NBand.M7500_7700.SplitData.node0813 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0814
  · rfl

def B0812 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0813, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0812 : B0812.tree = HexagonCover.NBand.M7500_7700.SplitData.node0812 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0813
  · rfl
  · rfl

def B0799 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0800, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0812]
theorem treeEq0799 : B0799.tree = HexagonCover.NBand.M7500_7700.SplitData.node0799 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0800
  · rfl
  · rfl
  · rfl
  · exact treeEq0812

theorem accepted0799 : B0799.accepted = true := by decide +kernel
theorem checked0799 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0799 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0799]
  exact B0799.sound accepted0799
#print axioms checked0799

def Tip0761_0762 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0762 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0008.checked0762
def B0787 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0787 : B0787.tree = HexagonCover.NBand.M7500_7700.SplitData.node0787 := by
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

def B0786 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0787]
theorem treeEq0786 : B0786.tree = HexagonCover.NBand.M7500_7700.SplitData.node0786 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0787

def B0785 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0786, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0785 : B0785.tree = HexagonCover.NBand.M7500_7700.SplitData.node0785 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0786
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0784 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0785, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0784 : B0784.tree = HexagonCover.NBand.M7500_7700.SplitData.node0784 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0785
  · rfl

def B0783 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0784, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0783 : B0783.tree = HexagonCover.NBand.M7500_7700.SplitData.node0783 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0784
  · rfl
  · rfl

def B0782 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0783]
theorem treeEq0782 : B0782.tree = HexagonCover.NBand.M7500_7700.SplitData.node0782 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0783

def B0792 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0792 : B0792.tree = HexagonCover.NBand.M7500_7700.SplitData.node0792 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0791 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0792, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0791 : B0791.tree = HexagonCover.NBand.M7500_7700.SplitData.node0791 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0792
  · rfl

def B0790 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0791, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0790 : B0790.tree = HexagonCover.NBand.M7500_7700.SplitData.node0790 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0791
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0789 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0790, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0789 : B0789.tree = HexagonCover.NBand.M7500_7700.SplitData.node0789 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0790
  · rfl

def B0788 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 38690348594151003235835912, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 856).pointIds 856), B0789, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0788 : B0788.tree = HexagonCover.NBand.M7500_7700.SplitData.node0788 := by
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

def B0781 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0782, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0788]
theorem treeEq0781 : B0781.tree = HexagonCover.NBand.M7500_7700.SplitData.node0781 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0782
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0788

def B0797 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0797 : B0797.tree = HexagonCover.NBand.M7500_7700.SplitData.node0797 := by
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

def B0796 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0797]
theorem treeEq0796 : B0796.tree = HexagonCover.NBand.M7500_7700.SplitData.node0796 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0797

def B0795 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0796, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0795 : B0795.tree = HexagonCover.NBand.M7500_7700.SplitData.node0795 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0796
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0794 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0795, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0794 : B0794.tree = HexagonCover.NBand.M7500_7700.SplitData.node0794 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0795
  · rfl

def B0793 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0794, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0793 : B0793.tree = HexagonCover.NBand.M7500_7700.SplitData.node0793 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0794
  · rfl
  · rfl

def B0780 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0781, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0793]
theorem treeEq0780 : B0780.tree = HexagonCover.NBand.M7500_7700.SplitData.node0780 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0781
  · rfl
  · rfl
  · rfl
  · exact treeEq0793

def B0761 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0761_0762, B0780, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0761 : B0761.tree = HexagonCover.NBand.M7500_7700.SplitData.node0761 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0780
  · rfl
  · rfl
  · rfl

theorem accepted0761 : B0761.accepted = true := by decide +kernel
theorem checked0761 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0761 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0761]
  exact B0761.sound accepted0761
#print axioms checked0761

def Tip0760_0799 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0799 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] checked0799
def Tip0760_0761 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0761 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] checked0761
def B0824 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0824 : B0824.tree = HexagonCover.NBand.M7500_7700.SplitData.node0824 := by
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

def B0823 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0824]
theorem treeEq0823 : B0823.tree = HexagonCover.NBand.M7500_7700.SplitData.node0823 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0824

def B0822 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0823, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0822 : B0822.tree = HexagonCover.NBand.M7500_7700.SplitData.node0822 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0823
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0821 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0822, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0821 : B0821.tree = HexagonCover.NBand.M7500_7700.SplitData.node0821 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0822
  · rfl

def B0820 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0821, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0820 : B0820.tree = HexagonCover.NBand.M7500_7700.SplitData.node0820 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0821
  · rfl
  · rfl

def B0819 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0820]
theorem treeEq0819 : B0819.tree = HexagonCover.NBand.M7500_7700.SplitData.node0819 := by
  change Tree.branch (88 : Fin 173) _ = Tree.branch (88 : Fin 173) _
  apply congrArg (Tree.branch (88 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0820

def B0829 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0829 : B0829.tree = HexagonCover.NBand.M7500_7700.SplitData.node0829 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0828 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0829, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0828 : B0828.tree = HexagonCover.NBand.M7500_7700.SplitData.node0828 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0829
  · rfl

def B0827 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0828, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0827 : B0827.tree = HexagonCover.NBand.M7500_7700.SplitData.node0827 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0828
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0826 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0827, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0826 : B0826.tree = HexagonCover.NBand.M7500_7700.SplitData.node0826 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0827
  · rfl

def B0825 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 38690348594151003235835912, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 856).pointIds 856), B0826, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0825 : B0825.tree = HexagonCover.NBand.M7500_7700.SplitData.node0825 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0826
  · rfl
  · rfl

def B0818 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0819, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0825]
theorem treeEq0818 : B0818.tree = HexagonCover.NBand.M7500_7700.SplitData.node0818 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0819
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0825

def B0834 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0834 : B0834.tree = HexagonCover.NBand.M7500_7700.SplitData.node0834 := by
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

def B0833 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0834]
theorem treeEq0833 : B0833.tree = HexagonCover.NBand.M7500_7700.SplitData.node0833 := by
  change Tree.branch (100 : Fin 173) _ = Tree.branch (100 : Fin 173) _
  apply congrArg (Tree.branch (100 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0834

def B0832 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0833, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0832 : B0832.tree = HexagonCover.NBand.M7500_7700.SplitData.node0832 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0833
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0831 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0832, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0831 : B0831.tree = HexagonCover.NBand.M7500_7700.SplitData.node0831 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0832
  · rfl

def B0830 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0831, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0830 : B0830.tree = HexagonCover.NBand.M7500_7700.SplitData.node0830 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0831
  · rfl
  · rfl

def B0817 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0818, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0830]
theorem treeEq0817 : B0817.tree = HexagonCover.NBand.M7500_7700.SplitData.node0817 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0818
  · rfl
  · rfl
  · rfl
  · exact treeEq0830

def B0798 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0760_0799, B0817, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0798 : B0798.tree = HexagonCover.NBand.M7500_7700.SplitData.node0798 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0817
  · rfl
  · rfl
  · rfl

def B0760 : Block := .branch 73 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0760_0761, B0798, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0760 : B0760.tree = HexagonCover.NBand.M7500_7700.SplitData.node0760 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0798
  · rfl
  · rfl
  · rfl

theorem accepted0760 : B0760.accepted = true := by decide +kernel
theorem checked0760 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0760 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0760]
  exact B0760.sound accepted0760
#print axioms checked0760

def Tip0596_0713 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0713 ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0008.checked0713
def Tip0596_0597 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0597 ![590295810358705652097, 148294669267544049154, 11861364525786298587140, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0008.checked0597
def B0754 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq0754 : B0754.tree = HexagonCover.NBand.M7500_7700.SplitData.node0754 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0753 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0754, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0753 : B0753.tree = HexagonCover.NBand.M7500_7700.SplitData.node0753 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0754
  · rfl

def B0752 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B0753, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0752 : B0752.tree = HexagonCover.NBand.M7500_7700.SplitData.node0752 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0753
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0751 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0752, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0751 : B0751.tree = HexagonCover.NBand.M7500_7700.SplitData.node0751 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0752
  · rfl

def B0750 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 38695070960633872881049608, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 852).pointIds 852), (.leaf 3 (Common.fact 853).pointIds 853), B0751, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0750 : B0750.tree = HexagonCover.NBand.M7500_7700.SplitData.node0750 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0751
  · rfl
  · rfl

def B0712 : Block := .branch 68 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), Tip0596_0713, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B0750]
theorem treeEq0712 : B0712.tree = HexagonCover.NBand.M7500_7700.SplitData.node0712 := by
  change Tree.branch (68 : Fin 173) _ = Tree.branch (68 : Fin 173) _
  apply congrArg (Tree.branch (68 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0750

def B0711 : Block := .branch 113 ![590295810358705652097, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![B0712, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0711 : B0711.tree = HexagonCover.NBand.M7500_7700.SplitData.node0711 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0712
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0710 : Block := .branch 144 ![590295810358705652097, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0711, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq0710 : B0710.tree = HexagonCover.NBand.M7500_7700.SplitData.node0710 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0711
  · rfl

def B0709 : Block := .branch 149 ![590295810358705652097, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0710, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0709 : B0709.tree = HexagonCover.NBand.M7500_7700.SplitData.node0709 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0710
  · rfl
  · rfl

def B0708 : Block := .branch 161 ![590295810358705652097, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0709]
theorem treeEq0708 : B0708.tree = HexagonCover.NBand.M7500_7700.SplitData.node0708 := by
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
  · exact treeEq0709

def B0596 : Block := .branch 73 ![590295810358705652097, 148294669267544049154, 7138998042916653373444, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0596_0597, B0708, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0596 : B0596.tree = HexagonCover.NBand.M7500_7700.SplitData.node0596 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0708
  · rfl
  · rfl
  · rfl

theorem accepted0596 : B0596.accepted = true := by decide +kernel
theorem checked0596 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0596 (maskNeeds ![590295810358705652097, 148294669267544049154, 7138998042916653373444, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0596]
  exact B0596.sound accepted0596
#print axioms checked0596

end HexagonCover.NBand.M7500_7700.SplitTree.Run0009
