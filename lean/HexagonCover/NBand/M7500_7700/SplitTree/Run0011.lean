import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.NBand.M7500_7700.SplitTree.Run0010
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0011
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0967 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0967 : B0967.tree = HexagonCover.NBand.M7500_7700.SplitData.node0967 := by
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

def B0966 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0967]
theorem treeEq0966 : B0966.tree = HexagonCover.NBand.M7500_7700.SplitData.node0966 := by
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
  · exact treeEq0967

def B0965 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0966, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0965 : B0965.tree = HexagonCover.NBand.M7500_7700.SplitData.node0965 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0966
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0964 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0965, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0964 : B0964.tree = HexagonCover.NBand.M7500_7700.SplitData.node0964 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0965
  · rfl

def B0963 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0964, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0963 : B0963.tree = HexagonCover.NBand.M7500_7700.SplitData.node0963 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0964
  · rfl
  · rfl

def B0962 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0963]
theorem treeEq0962 : B0962.tree = HexagonCover.NBand.M7500_7700.SplitData.node0962 := by
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
  · exact treeEq0963

def B0972 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0972 : B0972.tree = HexagonCover.NBand.M7500_7700.SplitData.node0972 := by
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

def B0971 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0972, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0971 : B0971.tree = HexagonCover.NBand.M7500_7700.SplitData.node0971 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0972
  · rfl

def B0970 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0971, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0970 : B0970.tree = HexagonCover.NBand.M7500_7700.SplitData.node0970 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0971
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0969 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0970, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0969 : B0969.tree = HexagonCover.NBand.M7500_7700.SplitData.node0969 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0970
  · rfl

def B0968 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 38687987410909568413229064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 859).pointIds 859), B0969, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0968 : B0968.tree = HexagonCover.NBand.M7500_7700.SplitData.node0968 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0969
  · rfl
  · rfl

def B0961 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0962, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0968]
theorem treeEq0961 : B0961.tree = HexagonCover.NBand.M7500_7700.SplitData.node0961 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0962
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0968

def B0977 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0977 : B0977.tree = HexagonCover.NBand.M7500_7700.SplitData.node0977 := by
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

def B0976 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0977]
theorem treeEq0976 : B0976.tree = HexagonCover.NBand.M7500_7700.SplitData.node0976 := by
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
  · exact treeEq0977

def B0975 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0976, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0975 : B0975.tree = HexagonCover.NBand.M7500_7700.SplitData.node0975 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0976
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0974 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0975, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0974 : B0974.tree = HexagonCover.NBand.M7500_7700.SplitData.node0974 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0975
  · rfl

def B0973 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0974, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0973 : B0973.tree = HexagonCover.NBand.M7500_7700.SplitData.node0973 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0974
  · rfl
  · rfl

def B0960 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0961, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0973]
theorem treeEq0960 : B0960.tree = HexagonCover.NBand.M7500_7700.SplitData.node0960 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0961
  · rfl
  · rfl
  · rfl
  · exact treeEq0973

theorem accepted0960 : B0960.accepted = true := by decide +kernel
theorem checked0960 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0960 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0960]
  exact B0960.sound accepted0960
#print axioms checked0960

def Tip0922_0923 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0923 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0010.checked0923
def B0948 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0948 : B0948.tree = HexagonCover.NBand.M7500_7700.SplitData.node0948 := by
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

def B0947 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0948]
theorem treeEq0947 : B0947.tree = HexagonCover.NBand.M7500_7700.SplitData.node0947 := by
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
  · exact treeEq0948

def B0946 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0947, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0946 : B0946.tree = HexagonCover.NBand.M7500_7700.SplitData.node0946 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0947
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0945 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0946, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0945 : B0945.tree = HexagonCover.NBand.M7500_7700.SplitData.node0945 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0946
  · rfl

def B0944 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0945, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0944 : B0944.tree = HexagonCover.NBand.M7500_7700.SplitData.node0944 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0945
  · rfl
  · rfl

def B0943 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0944]
theorem treeEq0943 : B0943.tree = HexagonCover.NBand.M7500_7700.SplitData.node0943 := by
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
  · exact treeEq0944

def B0953 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0953 : B0953.tree = HexagonCover.NBand.M7500_7700.SplitData.node0953 := by
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

def B0952 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0953, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0952 : B0952.tree = HexagonCover.NBand.M7500_7700.SplitData.node0952 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0953
  · rfl

def B0951 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0952, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0951 : B0951.tree = HexagonCover.NBand.M7500_7700.SplitData.node0951 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0952
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0950 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0951, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0950 : B0950.tree = HexagonCover.NBand.M7500_7700.SplitData.node0950 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0951
  · rfl

def B0949 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 38687987410909568413229064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 859).pointIds 859), B0950, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0949 : B0949.tree = HexagonCover.NBand.M7500_7700.SplitData.node0949 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0950
  · rfl
  · rfl

def B0942 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0943, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0949]
theorem treeEq0942 : B0942.tree = HexagonCover.NBand.M7500_7700.SplitData.node0942 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0943
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0949

def B0958 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0958 : B0958.tree = HexagonCover.NBand.M7500_7700.SplitData.node0958 := by
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

def B0957 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0958]
theorem treeEq0957 : B0957.tree = HexagonCover.NBand.M7500_7700.SplitData.node0957 := by
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
  · exact treeEq0958

def B0956 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0957, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0956 : B0956.tree = HexagonCover.NBand.M7500_7700.SplitData.node0956 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0957
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0955 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0956, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0955 : B0955.tree = HexagonCover.NBand.M7500_7700.SplitData.node0955 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0956
  · rfl

def B0954 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0955, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0954 : B0954.tree = HexagonCover.NBand.M7500_7700.SplitData.node0954 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0955
  · rfl
  · rfl

def B0941 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0942, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0954]
theorem treeEq0941 : B0941.tree = HexagonCover.NBand.M7500_7700.SplitData.node0941 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0942
  · rfl
  · rfl
  · rfl
  · exact treeEq0954

def B0922 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0922_0923, B0941, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0922 : B0922.tree = HexagonCover.NBand.M7500_7700.SplitData.node0922 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0941
  · rfl
  · rfl
  · rfl

theorem accepted0922 : B0922.accepted = true := by decide +kernel
theorem checked0922 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0922 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0922]
  exact B0922.sound accepted0922
#print axioms checked0922

def Tip0846_0885 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0885 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0010.checked0885
def Tip0846_0847 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0847 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] HexagonCover.NBand.M7500_7700.SplitTree.Run0010.checked0847
def B0910 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0910 : B0910.tree = HexagonCover.NBand.M7500_7700.SplitData.node0910 := by
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

def B0909 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0910]
theorem treeEq0909 : B0909.tree = HexagonCover.NBand.M7500_7700.SplitData.node0909 := by
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
  · exact treeEq0910

def B0908 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0909, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0908 : B0908.tree = HexagonCover.NBand.M7500_7700.SplitData.node0908 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0909
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0907 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0908, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0907 : B0907.tree = HexagonCover.NBand.M7500_7700.SplitData.node0907 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0908
  · rfl

def B0906 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0907, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0906 : B0906.tree = HexagonCover.NBand.M7500_7700.SplitData.node0906 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0907
  · rfl
  · rfl

def B0905 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0906]
theorem treeEq0905 : B0905.tree = HexagonCover.NBand.M7500_7700.SplitData.node0905 := by
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
  · exact treeEq0906

def B0915 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0915 : B0915.tree = HexagonCover.NBand.M7500_7700.SplitData.node0915 := by
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

def B0914 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0915, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0914 : B0914.tree = HexagonCover.NBand.M7500_7700.SplitData.node0914 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0915
  · rfl

def B0913 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0914, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0913 : B0913.tree = HexagonCover.NBand.M7500_7700.SplitData.node0913 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0914
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0912 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0913, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0912 : B0912.tree = HexagonCover.NBand.M7500_7700.SplitData.node0912 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0913
  · rfl

def B0911 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 38687987410909568413229064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 859).pointIds 859), B0912, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0911 : B0911.tree = HexagonCover.NBand.M7500_7700.SplitData.node0911 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0912
  · rfl
  · rfl

def B0904 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0905, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0911]
theorem treeEq0904 : B0904.tree = HexagonCover.NBand.M7500_7700.SplitData.node0904 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0905
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0911

def B0920 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0920 : B0920.tree = HexagonCover.NBand.M7500_7700.SplitData.node0920 := by
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

def B0919 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0920]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M7500_7700.SplitData.node0919 := by
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
  · exact treeEq0920

def B0918 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0919, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M7500_7700.SplitData.node0918 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0919
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0917 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0918, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M7500_7700.SplitData.node0917 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0918
  · rfl

def B0916 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0917, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0916 : B0916.tree = HexagonCover.NBand.M7500_7700.SplitData.node0916 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0917
  · rfl
  · rfl

def B0903 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0904, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0916]
theorem treeEq0903 : B0903.tree = HexagonCover.NBand.M7500_7700.SplitData.node0903 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0904
  · rfl
  · rfl
  · rfl
  · exact treeEq0916

def B0884 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0846_0885, B0903, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0884 : B0884.tree = HexagonCover.NBand.M7500_7700.SplitData.node0884 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0903
  · rfl
  · rfl
  · rfl

def B0846 : Block := .branch 73 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0846_0847, B0884, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0846 : B0846.tree = HexagonCover.NBand.M7500_7700.SplitData.node0846 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0884
  · rfl
  · rfl
  · rfl

theorem accepted0846 : B0846.accepted = true := by decide +kernel
theorem checked0846 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0846 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0846]
  exact B0846.sound accepted0846
#print axioms checked0846

def Tip0921_0960 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0960 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] checked0960
def Tip0921_0922 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0922 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] checked0922
def B0985 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320932304062383649012434389696576] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 833).pointIds 833)]
theorem treeEq0985 : B0985.tree = HexagonCover.NBand.M7500_7700.SplitData.node0985 := by
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

def B0984 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664653462155419610937686491200] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0985]
theorem treeEq0984 : B0984.tree = HexagonCover.NBand.M7500_7700.SplitData.node0984 := by
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
  · exact treeEq0985

def B0983 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664653462155419610937686491200] ![B0984, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 831).pointIds 831)]
theorem treeEq0983 : B0983.tree = HexagonCover.NBand.M7500_7700.SplitData.node0983 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0984
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0982 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0983, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0982 : B0982.tree = HexagonCover.NBand.M7500_7700.SplitData.node0982 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0983
  · rfl

def B0981 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664808204660330283472048881728] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0982, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 829).pointIds 829)]
theorem treeEq0981 : B0981.tree = HexagonCover.NBand.M7500_7700.SplitData.node0981 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0982
  · rfl
  · rfl

def B0980 : Block := .branch 88 ![10384593717070245552871351364092289, 302231599159582857889282, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 720).pointIds 720), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0981]
theorem treeEq0980 : B0980.tree = HexagonCover.NBand.M7500_7700.SplitData.node0980 := by
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
  · exact treeEq0981

def B0990 : Block := .branch 125 ![590295810358705652097, 1538, 6148, 24584, 98320, 2854495385411919762116571938898990272765886496, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 454).pointIds 454), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 844).pointIds 844)]
theorem treeEq0990 : B0990.tree = HexagonCover.NBand.M7500_7700.SplitData.node0990 := by
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

def B0989 : Block := .branch 151 ![590295810358705652097, 1538, 6148, 24584, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664344279377053169526255386688] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 842).pointIds 842), B0990, (.leaf 6 (Common.fact 843).pointIds 843)]
theorem treeEq0989 : B0989.tree = HexagonCover.NBand.M7500_7700.SplitData.node0989 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0990
  · rfl

def B0988 : Block := .branch 170 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344279377053169526255386688] ![B0989, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq0988 : B0988.tree = HexagonCover.NBand.M7500_7700.SplitData.node0988 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0989
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0987 : Block := .branch 171 ![590295810358705652097, 144255925564212738, 18518801667747485700, 38685626227668133590622216, 5986310706507378352962293074805895248510699696128016, 393248, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 840).pointIds 840), B0988, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0987 : B0987.tree = HexagonCover.NBand.M7500_7700.SplitData.node0987 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0988
  · rfl

def B0986 : Block := .branch 172 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 38687987410909568413229064, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664499021881963842060617777216] ![(.leaf 0 (Common.fact 834).pointIds 834), (.leaf 1 (Common.fact 835).pointIds 835), (.leaf 2 (Common.fact 858).pointIds 858), (.leaf 3 (Common.fact 859).pointIds 859), B0987, (.leaf 5 (Common.fact 838).pointIds 838), (.leaf 6 (Common.fact 839).pointIds 839)]
theorem treeEq0986 : B0986.tree = HexagonCover.NBand.M7500_7700.SplitData.node0986 := by
  change Tree.branch (172 : Fin 173) _ = Tree.branch (172 : Fin 173) _
  apply congrArg (Tree.branch (172 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0987
  · rfl
  · rfl

def B0979 : Block := .branch 78 ![10384593717070245552871351364092289, 148294669267544049154, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 142).pointIds 142), B0980, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), B0986]
theorem treeEq0979 : B0979.tree = HexagonCover.NBand.M7500_7700.SplitData.node0979 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0980
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0986

def B0995 : Block := .branch 119 ![385, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877320931994652931691393279988334656] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), (.leaf 4 (Common.fact 650).pointIds 650), (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0995 : B0995.tree = HexagonCover.NBand.M7500_7700.SplitData.node0995 := by
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

def B0994 : Block := .branch 100 ![1496577676626844598625166985771719364999026288099713, 1538, 6148, 79247505327378171660339273736, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664344052703461991783285129280] ![(.leaf 0 (Common.fact 832).pointIds 832), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 476).pointIds 476), (.leaf 3 (Common.fact 477).pointIds 477), (.leaf 4 (Common.fact 478).pointIds 478), (.leaf 5 (Common.fact 479).pointIds 479), B0995]
theorem treeEq0994 : B0994.tree = HexagonCover.NBand.M7500_7700.SplitData.node0994 := by
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
  · exact treeEq0995

def B0993 : Block := .branch 170 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 2993155353253689176481146537402947624255349848408096, 2923003296439877319664344052703461991783285129280] ![B0994, (.leaf 1 (Common.fact 722).pointIds 722), (.leaf 2 (Common.fact 723).pointIds 723), (.leaf 3 (Common.fact 724).pointIds 724), (.leaf 4 (Common.fact 655).pointIds 655), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq0993 : B0993.tree = HexagonCover.NBand.M7500_7700.SplitData.node0993 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0994
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0992 : Block := .branch 171 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 5575186299632655785383929568162090376593424, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 726).pointIds 726), (.leaf 1 (Common.fact 727).pointIds 727), (.leaf 2 (Common.fact 728).pointIds 728), (.leaf 3 (Common.fact 729).pointIds 729), (.leaf 4 (Common.fact 830).pointIds 830), B0993, (.leaf 6 (Common.fact 661).pointIds 661)]
theorem treeEq0992 : B0992.tree = HexagonCover.NBand.M7500_7700.SplitData.node0992 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0993
  · rfl

def B0991 : Block := .branch 142 ![10384593717070245552871351364092289, 144255925564212738, 18518801667747485700, 79286190953605839793929871368, 98320, 393248, 2923003296439877319664498795208372664317647519808] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), B0992, (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq0991 : B0991.tree = HexagonCover.NBand.M7500_7700.SplitData.node0991 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0992
  · rfl
  · rfl

def B0978 : Block := .branch 76 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 828).pointIds 828), B0979, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), B0991]
theorem treeEq0978 : B0978.tree = HexagonCover.NBand.M7500_7700.SplitData.node0978 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0979
  · rfl
  · rfl
  · rfl
  · exact treeEq0991

def B0959 : Block := .branch 74 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), Tip0921_0960, B0978, (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0959 : B0959.tree = HexagonCover.NBand.M7500_7700.SplitData.node0959 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0978
  · rfl
  · rfl
  · rfl

def B0921 : Block := .branch 73 ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), Tip0921_0922, B0959, (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0921 : B0921.tree = HexagonCover.NBand.M7500_7700.SplitData.node0921 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0959
  · rfl
  · rfl
  · rfl

theorem accepted0921 : B0921.accepted = true := by decide +kernel
theorem checked0921 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0921 (maskNeeds ![10384593717070245552871351364092289, 443442574446896875010, 55412289815166588932, 79286193314789081228752478216, 98320, 22300745198530623141535718272648361506373664, 2923003296439877319664498719650508938403324100672]) := by
  rw [← treeEq0921]
  exact B0921.sound accepted0921
#print axioms checked0921

end HexagonCover.NBand.M7500_7700.SplitTree.Run0011
