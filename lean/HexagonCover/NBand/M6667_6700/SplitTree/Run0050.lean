import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0048
import HexagonCover.NBand.M6667_6700.SplitTree.Run0049
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0050
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip3532_3534 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3534 ![2596148429267414967186752771457409, 1538, 36893489246930737156, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] HexagonCover.NBand.M6667_6700.SplitTree.Run0049.checked3534
def B3636 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 5987772208144709258801163742640009936305223892467776] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 1283).pointIds 1283), (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 1284).pointIds 1284)]
theorem treeEq3636 : B3636.tree = HexagonCover.NBand.M6667_6700.SplitData.node3636 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3635 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 5987772208144709258801163742640009936305223892467776] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3636, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1282).pointIds 1282)]
theorem treeEq3635 : B3635.tree = HexagonCover.NBand.M6667_6700.SplitData.node3635 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3636
  · rfl
  · rfl

def B3634 : Block := .branch 160 ![385, 1538, 4759259972116575950852, 29016580853992535015579656, 696898287454081973172991196020261297160208, 393248, 5986310706507378355882960057807293653285567959924800] ![(.leaf 0 (Common.fact 236).pointIds 236), (.leaf 1 (Common.fact 237).pointIds 237), (.leaf 2 (Common.fact 1299).pointIds 1299), (.leaf 3 (Common.fact 1288).pointIds 1288), (.leaf 4 (Common.fact 238).pointIds 238), (.leaf 5 (Common.fact 239).pointIds 239), B3635]
theorem treeEq3634 : B3634.tree = HexagonCover.NBand.M6667_6700.SplitData.node3634 := by
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
  · exact treeEq3635

def B3640 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009333399012381324152930368] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 946).pointIds 946)]
theorem treeEq3640 : B3640.tree = HexagonCover.NBand.M6667_6700.SplitData.node3640 := by
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

def B3639 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B3640]
theorem treeEq3639 : B3639.tree = HexagonCover.NBand.M6667_6700.SplitData.node3639 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3640

def B3643 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358727183003789680518365248] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 948).pointIds 948)]
theorem treeEq3643 : B3643.tree = HexagonCover.NBand.M6667_6700.SplitData.node3643 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3642 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821324235379534330670350400] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B3643]
theorem treeEq3642 : B3642.tree = HexagonCover.NBand.M6667_6700.SplitData.node3642 := by
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
  · exact treeEq3643

def B3641 : Block := .branch 169 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713782171831437860810522688] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), B3642, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 947).pointIds 947)]
theorem treeEq3641 : B3641.tree = HexagonCover.NBand.M6667_6700.SplitData.node3641 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3642
  · rfl
  · rfl

def B3638 : Block := .branch 119 ![385, 1538, 1099511633924, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B3639, (.leaf 5 (Common.fact 419).pointIds 419), B3641]
theorem treeEq3638 : B3638.tree = HexagonCover.NBand.M6667_6700.SplitData.node3638 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3639
  · rfl
  · exact treeEq3641

def B3645 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155353950587463935228510575938820275611145175056, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 951).pointIds 951)]
theorem treeEq3645 : B3645.tree = HexagonCover.NBand.M6667_6700.SplitData.node3645 := by
  change Tree.branch (131 : Fin 173) _ = Tree.branch (131 : Fin 173) _
  apply congrArg (Tree.branch (131 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3644 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089505539251804250075920582734855536704] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3645, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 949).pointIds 949)]
theorem treeEq3644 : B3644.tree = HexagonCover.NBand.M6667_6700.SplitData.node3644 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3645
  · rfl
  · rfl

def B3637 : Block := .branch 112 ![385, 1538, 1099511633924, 19345174297075501617930248, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![B3638, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B3644]
theorem treeEq3637 : B3637.tree = HexagonCover.NBand.M6667_6700.SplitData.node3637 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3638
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3644

def B3633 : Block := .branch 72 ![385, 1538, 36893489246930737156, 29016580853992535015579656, 696898287454081973172991196020261297160208, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B3634, B3637, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 945).pointIds 945)]
theorem treeEq3633 : B3633.tree = HexagonCover.NBand.M6667_6700.SplitData.node3633 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3634
  · exact treeEq3637
  · rfl
  · rfl
  · rfl

def B3632 : Block := .branch 139 ![385, 1538, 36893489246930737156, 29016580853992535015579656, 98320, 393248, 6360455125664089502943103374982662106317486690926656] ![(.leaf 0 (Common.fact 684).pointIds 684), (.leaf 1 (Common.fact 685).pointIds 685), (.leaf 2 (Common.fact 686).pointIds 686), (.leaf 3 (Common.fact 687).pointIds 687), B3633, (.leaf 5 (Common.fact 688).pointIds 688), (.leaf 6 (Common.fact 944).pointIds 944)]
theorem treeEq3632 : B3632.tree = HexagonCover.NBand.M6667_6700.SplitData.node3632 := by
  change Tree.branch (139 : Fin 173) _ = Tree.branch (139 : Fin 173) _
  apply congrArg (Tree.branch (139 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3633
  · rfl
  · rfl

def B3533 : Block := .branch 111 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 522673715590561479879743397015195972894736, 393248, 6360455125664089501645979898299126371235985136025664] ![Tip3532_3534, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), B3632]
theorem treeEq3533 : B3533.tree = HexagonCover.NBand.M6667_6700.SplitData.node3533 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3632

def B3649 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1123164008288798892964684172976562205815952610164800] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1286).pointIds 1286)]
theorem treeEq3649 : B3649.tree = HexagonCover.NBand.M6667_6700.SplitData.node3649 := by
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

def B3648 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374875169975376598844397538625825299752115148161088] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3649]
theorem treeEq3648 : B3648.tree = HexagonCover.NBand.M6667_6700.SplitData.node3648 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3649

def B3647 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374875169975376600142471753259532206884739230466112] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3648, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1285).pointIds 1285)]
theorem treeEq3647 : B3647.tree = HexagonCover.NBand.M6667_6700.SplitData.node3647 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3648
  · rfl
  · rfl

def B3646 : Block := .branch 159 ![385, 618970609938500496155215362, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148683369910843174065374911264194624] ![(.leaf 0 (Common.fact 232).pointIds 232), (.leaf 1 (Common.fact 1269).pointIds 1269), (.leaf 2 (Common.fact 1250).pointIds 1250), (.leaf 3 (Common.fact 233).pointIds 233), (.leaf 4 (Common.fact 234).pointIds 234), (.leaf 5 (Common.fact 235).pointIds 235), B3647]
theorem treeEq3646 : B3646.tree = HexagonCover.NBand.M6667_6700.SplitData.node3646 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3647

def B3532 : Block := .branch 69 ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664] ![B3533, B3646, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 902).pointIds 902)]
theorem treeEq3532 : B3532.tree = HexagonCover.NBand.M6667_6700.SplitData.node3532 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3533
  · exact treeEq3646
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted3532 : B3532.accepted = true := by decide +kernel
theorem checked3532 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3532 (maskNeeds ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664]) := by
  rw [← treeEq3532]
  exact B3532.sound accepted3532
#print axioms checked3532

def Tip3525_3532 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3532 ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501645979898299126371235985136025664] checked3532
def B3531 : Block := .branch 132 ![385, 1538, 6148, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764357729643384042495148096] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 141).pointIds 141), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 901).pointIds 901)]
theorem treeEq3531 : B3531.tree = HexagonCover.NBand.M6667_6700.SplitData.node3531 := by
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

def B3530 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387130006992737320205033144384] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B3531]
theorem treeEq3530 : B3530.tree = HexagonCover.NBand.M6667_6700.SplitData.node3530 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3531

def B3529 : Block := .branch 108 ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B3530, (.leaf 5 (Common.fact 136).pointIds 136), Tip3525_3532]
theorem treeEq3529 : B3529.tree = HexagonCover.NBand.M6667_6700.SplitData.node3529 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3530
  · rfl
  · rfl

def B3652 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240258071987486287549956160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 957).pointIds 957)]
theorem treeEq3652 : B3652.tree = HexagonCover.NBand.M6667_6700.SplitData.node3652 := by
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

def B3651 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605907335081422450087952448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3652]
theorem treeEq3651 : B3651.tree = HexagonCover.NBand.M6667_6700.SplitData.node3651 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3652

def B3650 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820541041988555074170257472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3651, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 956).pointIds 956)]
theorem treeEq3650 : B3650.tree = HexagonCover.NBand.M6667_6700.SplitData.node3650 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3651
  · rfl
  · rfl

def B3528 : Block := .branch 101 ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B3529, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B3650]
theorem treeEq3528 : B3528.tree = HexagonCover.NBand.M6667_6700.SplitData.node3528 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3529
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3650

def B3655 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180749340131798850933144245764160] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 959).pointIds 959)]
theorem treeEq3655 : B3655.tree = HexagonCover.NBand.M6667_6700.SplitData.node3655 := by
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

def B3654 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060462705781061944869306783760448] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3655]
theorem treeEq3654 : B3654.tree = HexagonCover.NBand.M6667_6700.SplitData.node3654 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3655

def B3653 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358536920414768852001930866065472] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3654, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 958).pointIds 958)]
theorem treeEq3653 : B3653.tree = HexagonCover.NBand.M6667_6700.SplitData.node3653 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3654
  · rfl
  · rfl

def B3527 : Block := .branch 91 ![1152921504606847361, 618970019642690137449563650, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![B3528, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B3653]
theorem treeEq3527 : B3527.tree = HexagonCover.NBand.M6667_6700.SplitData.node3527 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3528
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3653

def B3658 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040558027635171373431593107520] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 961).pointIds 961)]
theorem treeEq3658 : B3658.tree = HexagonCover.NBand.M6667_6700.SplitData.node3658 := by
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

def B3657 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923676898265309594131103808] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3658]
theorem treeEq3657 : B3657.tree = HexagonCover.NBand.M6667_6700.SplitData.node3657 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3658

def B3656 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138310605172442218213408832] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3657, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 960).pointIds 960)]
theorem treeEq3656 : B3656.tree = HexagonCover.NBand.M6667_6700.SplitData.node3656 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3657
  · rfl
  · rfl

def B3526 : Block := .branch 89 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 117).pointIds 117), B3527, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B3656]
theorem treeEq3526 : B3526.tree = HexagonCover.NBand.M6667_6700.SplitData.node3526 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3527
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3656

def B3661 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929078925041369935500542016] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 963).pointIds 963)]
theorem treeEq3661 : B3661.tree = HexagonCover.NBand.M6667_6700.SplitData.node3661 := by
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

def B3660 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294728188135306098038538304] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3661]
theorem treeEq3660 : B3660.tree = HexagonCover.NBand.M6667_6700.SplitData.node3660 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3661

def B3659 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461422011952099789096296644672] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3660, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 962).pointIds 962)]
theorem treeEq3659 : B3659.tree = HexagonCover.NBand.M6667_6700.SplitData.node3659 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3660
  · rfl
  · rfl

def B3525 : Block := .branch 86 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), B3526, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B3659]
theorem treeEq3525 : B3525.tree = HexagonCover.NBand.M6667_6700.SplitData.node3525 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3526
  · rfl
  · rfl
  · exact treeEq3659

theorem accepted3525 : B3525.accepted = true := by decide +kernel
theorem checked3525 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3525 (maskNeeds ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408]) := by
  rw [← treeEq3525]
  exact B3525.sound accepted3525
#print axioms checked3525

def Tip3520_3525 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3525 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] checked3525
def B3664 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6734599544820800647083213573217930360669883178942528] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 965).pointIds 965)]
theorem treeEq3664 : B3664.tree = HexagonCover.NBand.M6667_6700.SplitData.node3664 := by
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

def B3663 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 5986310706507378352962926938867193454606045716938816] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3664]
theorem treeEq3663 : B3663.tree = HexagonCover.NBand.M6667_6700.SplitData.node3663 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3664

def B3662 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 5986310706507378354261001153500900361738669799243840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3663, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 964).pointIds 964)]
theorem treeEq3662 : B3662.tree = HexagonCover.NBand.M6667_6700.SplitData.node3662 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3663
  · rfl
  · rfl

def B3524 : Block := .branch 85 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357334596892080531744451235759388980068581392, 393248, 6360455125664089501321461344640699644452829115449408] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), Tip3520_3525, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B3662]
theorem treeEq3524 : B3524.tree = HexagonCover.NBand.M6667_6700.SplitData.node3524 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3662

def B3523 : Block := .branch 137 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 357160372320217011251157987960383914744315920, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), B3524, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq3523 : B3523.tree = HexagonCover.NBand.M6667_6700.SplitData.node3523 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3524
  · rfl
  · rfl

def B3522 : Block := .branch 138 ![1152921504606847361, 1538, 36893489246930737156, 29016580853992535015579656, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), B3523, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq3522 : B3522.tree = HexagonCover.NBand.M6667_6700.SplitData.node3522 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3523
  · rfl
  · rfl

def B3667 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 5986310706507378354261001134158087247904603003945024] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 969).pointIds 969)]
theorem treeEq3667 : B3667.tree = HexagonCover.NBand.M6667_6700.SplitData.node3667 := by
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

def B3666 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3667, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3666 : B3666.tree = HexagonCover.NBand.M6667_6700.SplitData.node3666 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3667
  · rfl
  · rfl

def B3665 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461363983512758286895910748224] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3666, (.leaf 6 (Common.fact 968).pointIds 968)]
theorem treeEq3665 : B3665.tree = HexagonCover.NBand.M6667_6700.SplitData.node3665 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3666
  · rfl

def B3521 : Block := .branch 84 ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3522, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3665]
theorem treeEq3521 : B3521.tree = HexagonCover.NBand.M6667_6700.SplitData.node3521 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3522
  · rfl
  · rfl
  · exact treeEq3665

def B3670 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445743616100856010242523200] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 971).pointIds 971)]
theorem treeEq3670 : B3670.tree = HexagonCover.NBand.M6667_6700.SplitData.node3670 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3669 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3670, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1052).pointIds 1052)]
theorem treeEq3669 : B3669.tree = HexagonCover.NBand.M6667_6700.SplitData.node3669 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3670
  · rfl
  · rfl

def B3668 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 6360455125664089501321461345849625464067458290155584] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3669, (.leaf 6 (Common.fact 970).pointIds 970)]
theorem treeEq3668 : B3668.tree = HexagonCover.NBand.M6667_6700.SplitData.node3668 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3669
  · rfl

def B3520 : Block := .branch 80 ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464] ![B3521, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3668]
theorem treeEq3520 : B3520.tree = HexagonCover.NBand.M6667_6700.SplitData.node3520 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3521
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3668

theorem accepted3520 : B3520.accepted = true := by decide +kernel
theorem checked3520 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3520 (maskNeeds ![1152921504606847361, 1538, 55340233320640288772, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654125709465797897840230464]) := by
  rw [← treeEq3520]
  exact B3520.sound accepted3520
#print axioms checked3520

def Tip3348_3350 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node3350 ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] HexagonCover.NBand.M6667_6700.SplitTree.Run0048.checked3350
def B3506 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 1049).pointIds 1049)]
theorem treeEq3506 : B3506.tree = HexagonCover.NBand.M6667_6700.SplitData.node3506 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3505 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156713806814526015499804044744216479793216] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3506, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1048).pointIds 1048)]
theorem treeEq3505 : B3505.tree = HexagonCover.NBand.M6667_6700.SplitData.node3505 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3506
  · rfl
  · rfl

def B3504 : Block := .branch 121 ![385, 1538, 1099511633924, 24584, 713623846352979940529142984724747568191471632, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445668058237130095919104064] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 430).pointIds 430), B3505]
theorem treeEq3504 : B3504.tree = HexagonCover.NBand.M6667_6700.SplitData.node3504 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3505

def B3503 : Block := .branch 149 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 204).pointIds 204), (.leaf 1 (Common.fact 205).pointIds 205), (.leaf 2 (Common.fact 206).pointIds 206), (.leaf 3 (Common.fact 207).pointIds 207), B3504, (.leaf 5 (Common.fact 1046).pointIds 1046), (.leaf 6 (Common.fact 1047).pointIds 1047)]
theorem treeEq3503 : B3503.tree = HexagonCover.NBand.M6667_6700.SplitData.node3503 := by
  change Tree.branch (149 : Fin 173) _ = Tree.branch (149 : Fin 173) _
  apply congrArg (Tree.branch (149 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3504
  · rfl
  · rfl

def B3502 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148359168580453182173175912995487808] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3503, (.leaf 6 (Common.fact 1045).pointIds 1045)]
theorem treeEq3502 : B3502.tree = HexagonCover.NBand.M6667_6700.SplitData.node3502 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3503
  · rfl

def B3349 : Block := .branch 80 ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![Tip3348_3350, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3502]
theorem treeEq3349 : B3349.tree = HexagonCover.NBand.M6667_6700.SplitData.node3349 := by
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
  · exact treeEq3502

def B3512 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 1122433257470133441180746864478393871350337417773120] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 871).pointIds 871)]
theorem treeEq3512 : B3512.tree = HexagonCover.NBand.M6667_6700.SplitData.node3512 := by
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

def B3511 : Block := .branch 169 ![385, 1538, 1099511633924, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 374144419156711147060460230127656965286499955769408] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1254).pointIds 1254), (.leaf 2 (Common.fact 1255).pointIds 1255), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B3512]
theorem treeEq3511 : B3511.tree = HexagonCover.NBand.M6667_6700.SplitData.node3511 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3512

def B3510 : Block := .branch 171 ![385, 1538, 1099511633924, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1267).pointIds 1267), (.leaf 2 (Common.fact 1268).pointIds 1268), (.leaf 3 (Common.fact 1014).pointIds 1014), B3511, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1051).pointIds 1051)]
theorem treeEq3510 : B3510.tree = HexagonCover.NBand.M6667_6700.SplitData.node3510 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3511
  · rfl
  · rfl

def B3515 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 880).pointIds 880)]
theorem treeEq3515 : B3515.tree = HexagonCover.NBand.M6667_6700.SplitData.node3515 := by
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

def B3514 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3515, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 879).pointIds 879)]
theorem treeEq3514 : B3514.tree = HexagonCover.NBand.M6667_6700.SplitData.node3514 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3515
  · rfl
  · rfl

def B3513 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148358217551454119928902816657571904] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3514, (.leaf 6 (Common.fact 876).pointIds 876)]
theorem treeEq3513 : B3513.tree = HexagonCover.NBand.M6667_6700.SplitData.node3513 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3514
  · rfl

def B3509 : Block := .branch 84 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 1257).pointIds 1257), B3510, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B3513]
theorem treeEq3509 : B3509.tree = HexagonCover.NBand.M6667_6700.SplitData.node3509 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3510
  · rfl
  · rfl
  · exact treeEq3513

def B3518 : Block := .branch 108 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 136).pointIds 136), (.leaf 6 (Common.fact 883).pointIds 883)]
theorem treeEq3518 : B3518.tree = HexagonCover.NBand.M6667_6700.SplitData.node3518 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3517 : Block := .branch 167 ![385, 1538, 1099511633924, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1260).pointIds 1260), (.leaf 2 (Common.fact 1261).pointIds 1261), (.leaf 3 (Common.fact 1176).pointIds 1176), B3518, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 882).pointIds 882)]
theorem treeEq3517 : B3517.tree = HexagonCover.NBand.M6667_6700.SplitData.node3517 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3518
  · rfl
  · rfl

def B3516 : Block := .branch 170 ![385, 1538, 1099511633924, 24584, 98320, 393248, 374144419156711148358534445970289692033753212780608] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1258).pointIds 1258), (.leaf 2 (Common.fact 1259).pointIds 1259), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B3517, (.leaf 6 (Common.fact 881).pointIds 881)]
theorem treeEq3516 : B3516.tree = HexagonCover.NBand.M6667_6700.SplitData.node3516 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3517
  · rfl

def B3508 : Block := .branch 80 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![B3509, (.leaf 1 (Common.fact 92).pointIds 92), (.leaf 2 (Common.fact 93).pointIds 93), (.leaf 3 (Common.fact 94).pointIds 94), (.leaf 4 (Common.fact 95).pointIds 95), (.leaf 5 (Common.fact 96).pointIds 96), B3516]
theorem treeEq3508 : B3508.tree = HexagonCover.NBand.M6667_6700.SplitData.node3508 := by
  change Tree.branch (80 : Fin 173) _ = Tree.branch (80 : Fin 173) _
  apply congrArg (Tree.branch (80 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq3509
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3516

def B3507 : Block := .branch 95 ![385, 1538, 18446745173221185540, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 374144419156711148358534444761363872419124038074432] ![(.leaf 0 (Common.fact 851).pointIds 851), (.leaf 1 (Common.fact 852).pointIds 852), (.leaf 2 (Common.fact 1272).pointIds 1272), B3508, (.leaf 4 (Common.fact 854).pointIds 854), (.leaf 5 (Common.fact 855).pointIds 855), (.leaf 6 (Common.fact 1050).pointIds 1050)]
theorem treeEq3507 : B3507.tree = HexagonCover.NBand.M6667_6700.SplitData.node3507 := by
  change Tree.branch (95 : Fin 173) _ = Tree.branch (95 : Fin 173) _
  apply congrArg (Tree.branch (95 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3508
  · rfl
  · rfl
  · rfl

def B3348 : Block := .branch 78 ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 87).pointIds 87), B3349, (.leaf 2 (Common.fact 88).pointIds 88), (.leaf 3 (Common.fact 89).pointIds 89), (.leaf 4 (Common.fact 90).pointIds 90), (.leaf 5 (Common.fact 91).pointIds 91), B3507]
theorem treeEq3348 : B3348.tree = HexagonCover.NBand.M6667_6700.SplitData.node3348 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3349
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3507

theorem accepted3348 : B3348.accepted = true := by decide +kernel
theorem checked3348 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node3348 (maskNeeds ![1152921504606847361, 1538, 75576310471087544604676, 9673767740158468220280840, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq3348]
  exact B3348.sound accepted3348
#print axioms checked3348

end HexagonCover.NBand.M6667_6700.SplitTree.Run0050
