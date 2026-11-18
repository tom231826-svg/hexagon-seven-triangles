import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0007
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0008
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0721 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0721 : B0721.tree = HexagonCover.NBand.M7500_7700.SplitData.node0721 := by
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

def B0720 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0721]
theorem treeEq0720 : B0720.tree = HexagonCover.NBand.M7500_7700.SplitData.node0720 := by
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
  · exact treeEq0721

def B0719 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0720, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0719 : B0719.tree = HexagonCover.NBand.M7500_7700.SplitData.node0719 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0720
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0718 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0719, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0718 : B0718.tree = HexagonCover.NBand.M7500_7700.SplitData.node0718 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0719
  · rfl

def B0717 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0718, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0717 : B0717.tree = HexagonCover.NBand.M7500_7700.SplitData.node0717 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0718
  · rfl
  · rfl

def B0716 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0717]
theorem treeEq0716 : B0716.tree = HexagonCover.NBand.M7500_7700.SplitData.node0716 := by
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
  · exact treeEq0717

def B0726 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0726 : B0726.tree = HexagonCover.NBand.M7500_7700.SplitData.node0726 := by
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

def B0725 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0726, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0725 : B0725.tree = HexagonCover.NBand.M7500_7700.SplitData.node0725 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0726
  · rfl

def B0724 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0725, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0724 : B0724.tree = HexagonCover.NBand.M7500_7700.SplitData.node0724 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0725
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0723 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0724, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0723 : B0723.tree = HexagonCover.NBand.M7500_7700.SplitData.node0723 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0724
  · rfl

def B0722 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 38695070960633872881049608, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 852).pointIds 852), (.leaf 3 (Common.fact 853).pointIds 853), B0723, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0722 : B0722.tree = HexagonCover.NBand.M7500_7700.SplitData.node0722 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0723
  · rfl
  · rfl

def B0715 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0716, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0722]
theorem treeEq0715 : B0715.tree = HexagonCover.NBand.M7500_7700.SplitData.node0715 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0716
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0722

def B0731 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0731 : B0731.tree = HexagonCover.NBand.M7500_7700.SplitData.node0731 := by
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

def B0730 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0731]
theorem treeEq0730 : B0730.tree = HexagonCover.NBand.M7500_7700.SplitData.node0730 := by
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
  · exact treeEq0731

def B0729 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0730, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0729 : B0729.tree = HexagonCover.NBand.M7500_7700.SplitData.node0729 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0730
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0728 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0729, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0728 : B0728.tree = HexagonCover.NBand.M7500_7700.SplitData.node0728 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0729
  · rfl

def B0727 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0728, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0727 : B0727.tree = HexagonCover.NBand.M7500_7700.SplitData.node0727 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0728
  · rfl
  · rfl

def B0714 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0715, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0727]
theorem treeEq0714 : B0714.tree = HexagonCover.NBand.M7500_7700.SplitData.node0714 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0715
  · rfl
  · rfl
  · rfl
  · exact treeEq0727

theorem accepted0714 : B0714.accepted = true := by decide +kernel
theorem checked0714 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0714 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0714]
  exact B0714.sound accepted0714
#print axioms checked0714

def Tip0713_0714 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0714 ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] checked0714
def B0739 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0739 : B0739.tree = HexagonCover.NBand.M7500_7700.SplitData.node0739 := by
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

def B0738 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0739]
theorem treeEq0738 : B0738.tree = HexagonCover.NBand.M7500_7700.SplitData.node0738 := by
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
  · exact treeEq0739

def B0737 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0738, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0737 : B0737.tree = HexagonCover.NBand.M7500_7700.SplitData.node0737 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0738
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0736 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0737, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0736 : B0736.tree = HexagonCover.NBand.M7500_7700.SplitData.node0736 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0737
  · rfl

def B0735 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0736, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0735 : B0735.tree = HexagonCover.NBand.M7500_7700.SplitData.node0735 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0736
  · rfl
  · rfl

def B0734 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0735]
theorem treeEq0734 : B0734.tree = HexagonCover.NBand.M7500_7700.SplitData.node0734 := by
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
  · exact treeEq0735

def B0744 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0744 : B0744.tree = HexagonCover.NBand.M7500_7700.SplitData.node0744 := by
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

def B0743 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0744, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0743 : B0743.tree = HexagonCover.NBand.M7500_7700.SplitData.node0743 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0744
  · rfl

def B0742 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0743, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0742 : B0742.tree = HexagonCover.NBand.M7500_7700.SplitData.node0742 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0743
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0741 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0742, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0741 : B0741.tree = HexagonCover.NBand.M7500_7700.SplitData.node0741 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0742
  · rfl

def B0740 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 38695070960633872881049608, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 852).pointIds 852), (.leaf 3 (Common.fact 853).pointIds 853), B0741, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0740 : B0740.tree = HexagonCover.NBand.M7500_7700.SplitData.node0740 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0741
  · rfl
  · rfl

def B0733 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0734, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0740]
theorem treeEq0733 : B0733.tree = HexagonCover.NBand.M7500_7700.SplitData.node0733 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0734
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0740

def B0749 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0749 : B0749.tree = HexagonCover.NBand.M7500_7700.SplitData.node0749 := by
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

def B0748 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0749]
theorem treeEq0748 : B0748.tree = HexagonCover.NBand.M7500_7700.SplitData.node0748 := by
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
  · exact treeEq0749

def B0747 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0748, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0747 : B0747.tree = HexagonCover.NBand.M7500_7700.SplitData.node0747 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0748
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0746 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0747, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0746 : B0746.tree = HexagonCover.NBand.M7500_7700.SplitData.node0746 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0747
  · rfl

def B0745 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0746, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0745 : B0745.tree = HexagonCover.NBand.M7500_7700.SplitData.node0745 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0746
  · rfl
  · rfl

def B0732 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0733, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0745]
theorem treeEq0732 : B0732.tree = HexagonCover.NBand.M7500_7700.SplitData.node0732 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0733
  · rfl
  · rfl
  · rfl
  · exact treeEq0745

def B0713 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0713_0714, B0732, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0713 : B0713.tree = HexagonCover.NBand.M7500_7700.SplitData.node0713 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0732
  · rfl
  · rfl
  · rfl

theorem accepted0713 : B0713.accepted = true := by decide +kernel
theorem checked0713 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0713 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 7138962014119634409476, 79286200398338805533220298760, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0713]
  exact B0713.sound accepted0713
#print axioms checked0713

def Tip0597_0599 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0599 ![590295810358705652097, 302231599159582857889282, 21306097491525589014532, 79266848140492005727134572552, 98320, 393248, 21778071483257129054217942899091459014720] HexagonCover.NBand.M7500_7700.SplitTree.Run0007.checked0599
def Tip0597_0685 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0685 ![10384593717070245552871351364092289, 443442574446896875010, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0007.checked0685
def B0679 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0679 : B0679.tree = HexagonCover.NBand.M7500_7700.SplitData.node0679 := by
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

def B0678 : Block := .branch 142 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0679, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 649).pointIds 649)]
theorem treeEq0678 : B0678.tree = HexagonCover.NBand.M7500_7700.SplitData.node0678 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0679
  · rfl
  · rfl

def B0677 : Block := .branch 144 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0678, (.leaf 6 (Common.fact 648).pointIds 648)]
theorem treeEq0677 : B0677.tree = HexagonCover.NBand.M7500_7700.SplitData.node0677 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0678
  · rfl

def B0676 : Block := .branch 149 ![385, 1538, 6148, 79247505327378171660339273736, 98320, 393248, 21778071483257129356449397802748752691264] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0677, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 647).pointIds 647)]
theorem treeEq0676 : B0676.tree = HexagonCover.NBand.M7500_7700.SplitData.node0676 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0677
  · rfl
  · rfl

def B0598 : Block := .branch 78 ![590295810358705652097, 144255925564212738, 21306097491525589014532, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 142).pointIds 142), Tip0597_0599, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0676]
theorem treeEq0598 : B0598.tree = HexagonCover.NBand.M7500_7700.SplitData.node0598 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0676

def B0707 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 850).pointIds 850)]
theorem treeEq0707 : B0707.tree = HexagonCover.NBand.M7500_7700.SplitData.node0707 := by
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

def B0706 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664343977440746171048314536000] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0707, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0706 : B0706.tree = HexagonCover.NBand.M7500_7700.SplitData.node0706 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0707
  · rfl

def B0705 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664343977440746171048314536000] ![B0706, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 849).pointIds 849)]
theorem treeEq0705 : B0705.tree = HexagonCover.NBand.M7500_7700.SplitData.node0705 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0706
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0704 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0705, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0704 : B0704.tree = HexagonCover.NBand.M7500_7700.SplitData.node0704 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0705
  · rfl

def B0703 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 11861328496989279623172, 38704515693599612171477000, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719945656843582676926528] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 836).pointIds 836), (.leaf 3 (Common.fact 837).pointIds 837), B0704, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 848).pointIds 848)]
theorem treeEq0703 : B0703.tree = HexagonCover.NBand.M7500_7700.SplitData.node0703 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0704
  · rfl
  · rfl

def B0684 : Block := .branch 68 ![10384593717070245552871351364092289, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 827).pointIds 827), Tip0597_0685, (.leaf 2 (Common.fact 703).pointIds 703), (.leaf 3 (Common.fact 704).pointIds 704), (.leaf 4 (Common.fact 705).pointIds 705), (.leaf 5 (Common.fact 706).pointIds 706), B0703]
theorem treeEq0684 : B0684.tree = HexagonCover.NBand.M7500_7700.SplitData.node0684 := by
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
  · exact treeEq0703

def B0683 : Block := .branch 113 ![590295810358705652097, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![B0684, (.leaf 1 (Common.fact 240).pointIds 240), (.leaf 2 (Common.fact 241).pointIds 241), (.leaf 3 (Common.fact 242).pointIds 242), (.leaf 4 (Common.fact 243).pointIds 243), (.leaf 5 (Common.fact 244).pointIds 244), (.leaf 6 (Common.fact 826).pointIds 826)]
theorem treeEq0683 : B0683.tree = HexagonCover.NBand.M7500_7700.SplitData.node0683 := by
  change Tree.branch (113 : Fin 173) _ = Tree.branch (113 : Fin 173) _
  apply congrArg (Tree.branch (113 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0684
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0682 : Block := .branch 144 ![590295810358705652097, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), (.leaf 4 (Common.fact 128).pointIds 128), B0683, (.leaf 6 (Common.fact 825).pointIds 825)]
theorem treeEq0682 : B0682.tree = HexagonCover.NBand.M7500_7700.SplitData.node0682 := by
  change Tree.branch (144 : Fin 173) _ = Tree.branch (144 : Fin 173) _
  apply congrArg (Tree.branch (144 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0683
  · rfl

def B0681 : Block := .branch 149 ![590295810358705652097, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 77).pointIds 77), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), B0682, (.leaf 5 (Common.fact 80).pointIds 80), (.leaf 6 (Common.fact 824).pointIds 824)]
theorem treeEq0681 : B0681.tree = HexagonCover.NBand.M7500_7700.SplitData.node0681 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0682
  · rfl
  · rfl

def B0680 : Block := .branch 161 ![590295810358705652097, 148294669267544049154, 11861328496989279623172, 79286209843071771272510726152, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 779).pointIds 779), (.leaf 3 (Common.fact 823).pointIds 823), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0681]
theorem treeEq0680 : B0680.tree = HexagonCover.NBand.M7500_7700.SplitData.node0680 := by
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
  · exact treeEq0681

def B0597 : Block := .branch 74 ![590295810358705652097, 148294669267544049154, 11861364525786298587140, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), B0598, B0680, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0597 : B0597.tree = HexagonCover.NBand.M7500_7700.SplitData.node0597 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0598
  · exact treeEq0680
  · rfl
  · rfl
  · rfl

theorem accepted0597 : B0597.accepted = true := by decide +kernel
theorem checked0597 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0597 (maskNeeds ![590295810358705652097, 148294669267544049154, 11861364525786298587140, 79286190953605839793929871368, 98320, 393248, 21778071483257129054217942899091459014720]) := by
  rw [← treeEq0597]
  exact B0597.sound accepted0597
#print axioms checked0597

def B0769 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0769 : B0769.tree = HexagonCover.NBand.M7500_7700.SplitData.node0769 := by
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

def B0768 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0769]
theorem treeEq0768 : B0768.tree = HexagonCover.NBand.M7500_7700.SplitData.node0768 := by
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
  · exact treeEq0769

def B0767 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0768, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0767 : B0767.tree = HexagonCover.NBand.M7500_7700.SplitData.node0767 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0768
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0766 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0767, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0766 : B0766.tree = HexagonCover.NBand.M7500_7700.SplitData.node0766 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0767
  · rfl

def B0765 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0766, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0765 : B0765.tree = HexagonCover.NBand.M7500_7700.SplitData.node0765 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0766
  · rfl
  · rfl

def B0764 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0765]
theorem treeEq0764 : B0764.tree = HexagonCover.NBand.M7500_7700.SplitData.node0764 := by
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
  · exact treeEq0765

def B0774 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0774 : B0774.tree = HexagonCover.NBand.M7500_7700.SplitData.node0774 := by
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

def B0773 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0774, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0773 : B0773.tree = HexagonCover.NBand.M7500_7700.SplitData.node0773 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0774
  · rfl

def B0772 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0773, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0772 : B0772.tree = HexagonCover.NBand.M7500_7700.SplitData.node0772 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0773
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0771 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0772, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0771 : B0771.tree = HexagonCover.NBand.M7500_7700.SplitData.node0771 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0772
  · rfl

def B0770 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 38690348594151003235835912, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 855).pointIds 855), (.leaf 3 (Common.fact 856).pointIds 856), B0771, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0770 : B0770.tree = HexagonCover.NBand.M7500_7700.SplitData.node0770 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0771
  · rfl
  · rfl

def B0763 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0764, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0770]
theorem treeEq0763 : B0763.tree = HexagonCover.NBand.M7500_7700.SplitData.node0763 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0764
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0770

def B0779 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0779 : B0779.tree = HexagonCover.NBand.M7500_7700.SplitData.node0779 := by
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

def B0778 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0779]
theorem treeEq0778 : B0778.tree = HexagonCover.NBand.M7500_7700.SplitData.node0778 := by
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
  · exact treeEq0779

def B0777 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0778, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0777 : B0777.tree = HexagonCover.NBand.M7500_7700.SplitData.node0777 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0778
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0776 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0777, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0776 : B0776.tree = HexagonCover.NBand.M7500_7700.SplitData.node0776 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0777
  · rfl

def B0775 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0776, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0775 : B0775.tree = HexagonCover.NBand.M7500_7700.SplitData.node0775 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0776
  · rfl
  · rfl

def B0762 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0763, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0775]
theorem treeEq0762 : B0762.tree = HexagonCover.NBand.M7500_7700.SplitData.node0762 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0763
  · rfl
  · rfl
  · rfl
  · exact treeEq0775

theorem accepted0762 : B0762.accepted = true := by decide +kernel
theorem checked0762 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0762 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 2416595531249989195780, 79286195675972322663575085064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0762]
  exact B0762.sound accepted0762
#print axioms checked0762

end HexagonCover.NBand.M7500_7700.SplitTree.Run0008
