import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0010
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0011
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip0036_0039 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0039 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 649037107316853453566312041250832, 393248, 21804656042855759979114051017388527714368] HexagonCover.NBand.M8300_8500.SplitTree.Run0010.checked0039
def Tip0036_0828 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0828 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 98320, 393248, 21804656044123410579342280418885230919744] HexagonCover.NBand.M8300_8500.SplitTree.Run0010.checked0828
def B0827 : Block := .branch 171 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 374144419222045362158000609477189831225680024043584] ![(.leaf 0 (Common.fact 695).pointIds 695), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 607).pointIds 607), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), (.leaf 6 (Common.fact 719).pointIds 719)]
theorem treeEq0827 : B0827.tree = HexagonCover.NBand.M8300_8500.SplitData.node0827 := by
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
  · rfl

def B0826 : Block := .branch 135 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 748288838313422294120286634350736906063837462396960, 374144419178489219192120486153877881474413692977216] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B0827]
theorem treeEq0826 : B0826.tree = HexagonCover.NBand.M8300_8500.SplitData.node0826 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0827

def B0825 : Block := .branch 169 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 179799758163153149078631728573227414642065424, 393248, 374144419178489219192120486153877881474413692977216] ![(.leaf 0 (Common.fact 697).pointIds 697), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 605).pointIds 605), (.leaf 4 (Common.fact 716).pointIds 716), B0826, (.leaf 6 (Common.fact 717).pointIds 717)]
theorem treeEq0825 : B0825.tree = HexagonCover.NBand.M8300_8500.SplitData.node0825 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0826
  · rfl

def B0824 : Block := .branch 140 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 374144419178489219192120486153877881474413692977216] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B0825, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 715).pointIds 715)]
theorem treeEq0824 : B0824.tree = HexagonCover.NBand.M8300_8500.SplitData.node0824 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0825
  · rfl
  · rfl

def B0823 : Block := .branch 144 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 374144419178489219192120486153877881474413692977216] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B0824, (.leaf 6 (Common.fact 709).pointIds 709)]
theorem treeEq0823 : B0823.tree = HexagonCover.NBand.M8300_8500.SplitData.node0823 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0824
  · rfl

def B0822 : Block := .branch 148 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 374144419178489219192120486153877881474413692977216] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B0823, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 708).pointIds 708)]
theorem treeEq0822 : B0822.tree = HexagonCover.NBand.M8300_8500.SplitData.node0822 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0823
  · rfl
  · rfl

def B0821 : Block := .branch 168 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 21778072131977168978509428442494961975360] ![(.leaf 0 (Common.fact 693).pointIds 693), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 602).pointIds 602), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B0822]
theorem treeEq0821 : B0821.tree = HexagonCover.NBand.M8300_8500.SplitData.node0821 := by
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
  · exact treeEq0822

def B0038 : Block := .branch 109 ![1267650600228808114048820314497, 151152620940525821756930, 53230514994906640848787460, 158456325028528675187087925256, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), Tip0036_0039, (.leaf 5 (Common.fact 211).pointIds 211), B0821]
theorem treeEq0038 : B0038.tree = HexagonCover.NBand.M8300_8500.SplitData.node0038 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0821

def B0037 : Block := .branch 100 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81327708820892342539772865044488, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![B0038, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), Tip0036_0828]
theorem treeEq0037 : B0037.tree = HexagonCover.NBand.M8300_8500.SplitData.node0037 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0038
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0854 : Block := .branch 120 ![385, 1538, 6148, 24584, 11150372599265311570767859136324180753088528, 393248, 21799339131031076640650964464334494236736] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), (.leaf 4 (Common.fact 784).pointIds 784), (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 785).pointIds 785)]
theorem treeEq0854 : B0854.tree = HexagonCover.NBand.M8300_8500.SplitData.node0854 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0853 : Block := .branch 143 ![385, 1538, 6148, 24584, 98320, 393248, 21799339131031076640650964464334494236736] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), B0854, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 783).pointIds 783)]
theorem treeEq0853 : B0853.tree = HexagonCover.NBand.M8300_8500.SplitData.node0853 := by
  change Tree.branch (143 : Fin 177) _ = Tree.branch (143 : Fin 177) _
  apply congrArg (Tree.branch (143 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0854
  · rfl
  · rfl

def B0852 : Block := .branch 144 ![385, 1538, 6148, 24584, 98320, 393248, 21799339131031076640650964464334494236736] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), (.leaf 4 (Common.fact 291).pointIds 291), B0853, (.leaf 6 (Common.fact 782).pointIds 782)]
theorem treeEq0852 : B0852.tree = HexagonCover.NBand.M8300_8500.SplitData.node0852 := by
  change Tree.branch (144 : Fin 177) _ = Tree.branch (144 : Fin 177) _
  apply congrArg (Tree.branch (144 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0853
  · rfl

def B0851 : Block := .branch 107 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656043014216304142579692575615615040] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B0852, (.leaf 4 (Common.fact 779).pointIds 779), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0851 : B0851.tree = HexagonCover.NBand.M8300_8500.SplitData.node0851 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0852
  · rfl
  · rfl
  · rfl

def B0850 : Block := .branch 118 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656043014216304142579692575615615040] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B0851, (.leaf 4 (Common.fact 773).pointIds 773), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq0850 : B0850.tree = HexagonCover.NBand.M8300_8500.SplitData.node0850 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0851
  · rfl
  · rfl
  · rfl

def B0849 : Block := .branch 128 ![385, 1538, 6148, 24584, 3032901347000164747248857685080177164813434896, 393248, 21804656043014216304142579692575615615040] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B0850, (.leaf 4 (Common.fact 767).pointIds 767), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq0849 : B0849.tree = HexagonCover.NBand.M8300_8500.SplitData.node0849 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0850
  · rfl
  · rfl
  · rfl

def B0848 : Block := .branch 151 ![385, 1538, 6148, 24584, 178405961588244985132285746181186892047941648, 393248, 21804656043014216304142579692575615615040] ![(.leaf 0 (Common.fact 296).pointIds 296), (.leaf 1 (Common.fact 297).pointIds 297), (.leaf 2 (Common.fact 298).pointIds 298), (.leaf 3 (Common.fact 299).pointIds 299), B0849, (.leaf 5 (Common.fact 300).pointIds 300), (.leaf 6 (Common.fact 763).pointIds 763)]
theorem treeEq0848 : B0848.tree = HexagonCover.NBand.M8300_8500.SplitData.node0848 := by
  change Tree.branch (151 : Fin 177) _ = Tree.branch (151 : Fin 177) _
  apply congrArg (Tree.branch (151 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0849
  · rfl
  · rfl

def B0036 : Block := .branch 97 ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B0037, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), B0848]
theorem treeEq0036 : B0036.tree = HexagonCover.NBand.M8300_8500.SplitData.node0036 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0037
  · rfl
  · rfl
  · exact treeEq0848

theorem accepted0036 : B0036.accepted = true := by decide +kernel
theorem checked0036 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0036 (maskNeeds ![1237940039864092827016233345, 151152620940525821756930, 53230514994906640848787460, 81169252495863813864585777143816, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0036]
  exact B0036.sound accepted0036
#print axioms checked0036

def B0879 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0879 : B0879.tree = HexagonCover.NBand.M8300_8500.SplitData.node0879 := by
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

def B0878 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 826).pointIds 826), (.leaf 3 (Common.fact 827).pointIds 827), (.leaf 4 (Common.fact 716).pointIds 716), B0879, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0878 : B0878.tree = HexagonCover.NBand.M8300_8500.SplitData.node0878 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0879
  · rfl

def B0877 : Block := .branch 171 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 824).pointIds 824), (.leaf 3 (Common.fact 825).pointIds 825), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B0878]
theorem treeEq0877 : B0877.tree = HexagonCover.NBand.M8300_8500.SplitData.node0877 := by
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
  · exact treeEq0878

def B0876 : Block := .branch 88 ![604463488519866704462209, 151152620940525821756930, 2923003274661805836407403553134447111885918574596, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 577).pointIds 577), B0877, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0876 : B0876.tree = HexagonCover.NBand.M8300_8500.SplitData.node0876 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0877
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0875 : Block := .branch 161 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0876, (.leaf 3 (Common.fact 820).pointIds 820), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq0875 : B0875.tree = HexagonCover.NBand.M8300_8500.SplitData.node0875 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0876
  · rfl
  · rfl
  · rfl
  · rfl

def B0874 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 374144430307083746325454887943227589356649239281728] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 817).pointIds 817), (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B0875]
theorem treeEq0874 : B0874.tree = HexagonCover.NBand.M8300_8500.SplitData.node0874 := by
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
  · exact treeEq0875

def B0873 : Block := .branch 97 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 374144430328867134720378089268375179460523526193216] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B0874, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq0873 : B0873.tree = HexagonCover.NBand.M8300_8500.SplitData.node0873 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0874
  · rfl
  · rfl
  · rfl

def B0872 : Block := .branch 107 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B0873, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0872 : B0872.tree = HexagonCover.NBand.M8300_8500.SplitData.node0872 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0873
  · rfl
  · rfl
  · rfl

def B0871 : Block := .branch 118 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B0872, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq0871 : B0871.tree = HexagonCover.NBand.M8300_8500.SplitData.node0871 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0872
  · rfl
  · rfl
  · rfl

def B0870 : Block := .branch 128 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B0871, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq0870 : B0870.tree = HexagonCover.NBand.M8300_8500.SplitData.node0870 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0871
  · rfl
  · rfl
  · rfl

def B0869 : Block := .branch 120 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0870, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0869 : B0869.tree = HexagonCover.NBand.M8300_8500.SplitData.node0869 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0870
  · rfl
  · rfl

def B0868 : Block := .branch 143 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B0869]
theorem treeEq0868 : B0868.tree = HexagonCover.NBand.M8300_8500.SplitData.node0868 := by
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
  · exact treeEq0869

def B0867 : Block := .branch 140 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B0868, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0867 : B0867.tree = HexagonCover.NBand.M8300_8500.SplitData.node0867 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0868
  · rfl
  · rfl

def B0866 : Block := .branch 148 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B0867, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0866 : B0866.tree = HexagonCover.NBand.M8300_8500.SplitData.node0866 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0867
  · rfl
  · rfl

def B0865 : Block := .branch 168 ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 807).pointIds 807), (.leaf 3 (Common.fact 808).pointIds 808), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B0866]
theorem treeEq0865 : B0865.tree = HexagonCover.NBand.M8300_8500.SplitData.node0865 := by
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
  · exact treeEq0866

theorem accepted0865 : B0865.accepted = true := by decide +kernel
theorem checked0865 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0865 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 33887701881072574053488644, 38685626227668133590622216, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0865]
  exact B0865.sound accepted0865
#print axioms checked0865

def B0894 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0894 : B0894.tree = HexagonCover.NBand.M8300_8500.SplitData.node0894 := by
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

def B0893 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 835).pointIds 835), (.leaf 3 (Common.fact 836).pointIds 836), (.leaf 4 (Common.fact 716).pointIds 716), B0894, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0893 : B0893.tree = HexagonCover.NBand.M8300_8500.SplitData.node0893 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0894
  · rfl

def B0892 : Block := .branch 171 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 823).pointIds 823), (.leaf 1 (Common.fact 680).pointIds 680), (.leaf 2 (Common.fact 833).pointIds 833), (.leaf 3 (Common.fact 834).pointIds 834), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B0893]
theorem treeEq0892 : B0892.tree = HexagonCover.NBand.M8300_8500.SplitData.node0892 := by
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
  · exact treeEq0893

def B0891 : Block := .branch 88 ![604463488519866704462209, 151152620940525821756930, 2923003274661805836407384210321333277819123275780, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 577).pointIds 577), B0892, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 822).pointIds 822)]
theorem treeEq0891 : B0891.tree = HexagonCover.NBand.M8300_8500.SplitData.node0891 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0892
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0890 : Block := .branch 161 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 1870722106933928334566028156644701401484324163289152] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0891, (.leaf 3 (Common.fact 832).pointIds 832), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 821).pointIds 821)]
theorem treeEq0890 : B0890.tree = HexagonCover.NBand.M8300_8500.SplitData.node0890 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0891
  · rfl
  · rfl
  · rfl
  · rfl

def B0889 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 374144430307083746325454887943227589356649239281728] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 830).pointIds 830), (.leaf 3 (Common.fact 831).pointIds 831), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B0890]
theorem treeEq0889 : B0889.tree = HexagonCover.NBand.M8300_8500.SplitData.node0889 := by
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
  · exact treeEq0890

def B0888 : Block := .branch 97 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 374144430328867134720378089268375179460523526193216] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B0889, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq0888 : B0888.tree = HexagonCover.NBand.M8300_8500.SplitData.node0888 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0889
  · rfl
  · rfl
  · rfl

def B0887 : Block := .branch 107 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B0888, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq0887 : B0887.tree = HexagonCover.NBand.M8300_8500.SplitData.node0887 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0888
  · rfl
  · rfl
  · rfl

def B0886 : Block := .branch 118 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 770).pointIds 770), (.leaf 1 (Common.fact 771).pointIds 771), (.leaf 2 (Common.fact 772).pointIds 772), B0887, (.leaf 4 (Common.fact 814).pointIds 814), (.leaf 5 (Common.fact 774).pointIds 774), (.leaf 6 (Common.fact 775).pointIds 775)]
theorem treeEq0886 : B0886.tree = HexagonCover.NBand.M8300_8500.SplitData.node0886 := by
  change Tree.branch (118 : Fin 177) _ = Tree.branch (118 : Fin 177) _
  apply congrArg (Tree.branch (118 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0887
  · rfl
  · rfl
  · rfl

def B0885 : Block := .branch 128 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 764).pointIds 764), (.leaf 1 (Common.fact 765).pointIds 765), (.leaf 2 (Common.fact 766).pointIds 766), B0886, (.leaf 4 (Common.fact 813).pointIds 813), (.leaf 5 (Common.fact 768).pointIds 768), (.leaf 6 (Common.fact 769).pointIds 769)]
theorem treeEq0885 : B0885.tree = HexagonCover.NBand.M8300_8500.SplitData.node0885 := by
  change Tree.branch (128 : Fin 177) _ = Tree.branch (128 : Fin 177) _
  apply congrArg (Tree.branch (128 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0886
  · rfl
  · rfl
  · rfl

def B0884 : Block := .branch 120 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 741).pointIds 741), (.leaf 1 (Common.fact 742).pointIds 742), (.leaf 2 (Common.fact 743).pointIds 743), (.leaf 3 (Common.fact 744).pointIds 744), B0885, (.leaf 5 (Common.fact 745).pointIds 745), (.leaf 6 (Common.fact 812).pointIds 812)]
theorem treeEq0884 : B0884.tree = HexagonCover.NBand.M8300_8500.SplitData.node0884 := by
  change Tree.branch (120 : Fin 177) _ = Tree.branch (120 : Fin 177) _
  apply congrArg (Tree.branch (120 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0885
  · rfl
  · rfl

def B0883 : Block := .branch 143 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 179799758163153149078631728573227414642065424, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 212).pointIds 212), (.leaf 1 (Common.fact 213).pointIds 213), (.leaf 2 (Common.fact 214).pointIds 214), (.leaf 3 (Common.fact 215).pointIds 215), (.leaf 4 (Common.fact 811).pointIds 811), (.leaf 5 (Common.fact 217).pointIds 217), B0884]
theorem treeEq0883 : B0883.tree = HexagonCover.NBand.M8300_8500.SplitData.node0883 := by
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
  · exact treeEq0884

def B0882 : Block := .branch 140 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 710).pointIds 710), (.leaf 1 (Common.fact 711).pointIds 711), (.leaf 2 (Common.fact 712).pointIds 712), (.leaf 3 (Common.fact 713).pointIds 713), B0883, (.leaf 5 (Common.fact 714).pointIds 714), (.leaf 6 (Common.fact 810).pointIds 810)]
theorem treeEq0882 : B0882.tree = HexagonCover.NBand.M8300_8500.SplitData.node0882 := by
  change Tree.branch (140 : Fin 177) _ = Tree.branch (140 : Fin 177) _
  apply congrArg (Tree.branch (140 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0883
  · rfl
  · rfl

def B0881 : Block := .branch 148 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 178405961588244985132285746181186892047941648, 393248, 374144419178515803102999077154482504049307258716224] ![(.leaf 0 (Common.fact 703).pointIds 703), (.leaf 1 (Common.fact 704).pointIds 704), (.leaf 2 (Common.fact 705).pointIds 705), (.leaf 3 (Common.fact 706).pointIds 706), B0882, (.leaf 5 (Common.fact 707).pointIds 707), (.leaf 6 (Common.fact 809).pointIds 809)]
theorem treeEq0881 : B0881.tree = HexagonCover.NBand.M8300_8500.SplitData.node0881 := by
  change Tree.branch (148 : Fin 177) _ = Tree.branch (148 : Fin 177) _
  apply congrArg (Tree.branch (148 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0882
  · rfl
  · rfl

def B0880 : Block := .branch 168 ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368] ![(.leaf 0 (Common.fact 804).pointIds 804), (.leaf 1 (Common.fact 678).pointIds 678), (.leaf 2 (Common.fact 828).pointIds 828), (.leaf 3 (Common.fact 829).pointIds 829), (.leaf 4 (Common.fact 702).pointIds 702), (.leaf 5 (Common.fact 561).pointIds 561), B0881]
theorem treeEq0880 : B0880.tree = HexagonCover.NBand.M8300_8500.SplitData.node0880 := by
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
  · exact treeEq0881

theorem accepted0880 : B0880.accepted = true := by decide +kernel
theorem checked0880 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0880 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 14544888767238507258189828, 79247505327378171660339273736, 178405961588244985132285746181186892047941648, 393248, 21804656042855759979114051017388527714368]) := by
  rw [← treeEq0880]
  exact B0880.sound accepted0880
#print axioms checked0880

def B0921 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0921 : B0921.tree = HexagonCover.NBand.M8300_8500.SplitData.node0921 := by
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

def B0920 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B0921, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0920 : B0920.tree = HexagonCover.NBand.M8300_8500.SplitData.node0920 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0921
  · rfl

def B0919 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B0920]
theorem treeEq0919 : B0919.tree = HexagonCover.NBand.M8300_8500.SplitData.node0919 := by
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
  · exact treeEq0920

def B0926 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0926 : B0926.tree = HexagonCover.NBand.M8300_8500.SplitData.node0926 := by
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

def B0925 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B0926, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0925 : B0925.tree = HexagonCover.NBand.M8300_8500.SplitData.node0925 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0926
  · rfl

def B0924 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0925]
theorem treeEq0924 : B0924.tree = HexagonCover.NBand.M8300_8500.SplitData.node0924 := by
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
  · exact treeEq0925

def B0923 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0924, (.leaf 0 [] 0)]
theorem treeEq0923 : B0923.tree = HexagonCover.NBand.M8300_8500.SplitData.node0923 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0924
  · rfl

def B0922 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0923, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0922 : B0922.tree = HexagonCover.NBand.M8300_8500.SplitData.node0922 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0923
  · rfl

def B0918 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0919, B0922, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0918 : B0918.tree = HexagonCover.NBand.M8300_8500.SplitData.node0918 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0919
  · exact treeEq0922
  · rfl
  · rfl

def B0930 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq0930 : B0930.tree = HexagonCover.NBand.M8300_8500.SplitData.node0930 := by
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

def B0929 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B0930, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq0929 : B0929.tree = HexagonCover.NBand.M8300_8500.SplitData.node0929 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0930
  · rfl

def B0928 : Block := .branch 170 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 816).pointIds 816), (.leaf 1 (Common.fact 684).pointIds 684), (.leaf 2 (Common.fact 848).pointIds 848), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B0929]
theorem treeEq0928 : B0928.tree = HexagonCover.NBand.M8300_8500.SplitData.node0928 := by
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
  · exact treeEq0929

def B0935 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq0935 : B0935.tree = HexagonCover.NBand.M8300_8500.SplitData.node0935 := by
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

def B0934 : Block := .branch 169 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 805).pointIds 805), (.leaf 1 (Common.fact 682).pointIds 682), (.leaf 2 (Common.fact 850).pointIds 850), (.leaf 3 (Common.fact 851).pointIds 851), (.leaf 4 (Common.fact 716).pointIds 716), B0935, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq0934 : B0934.tree = HexagonCover.NBand.M8300_8500.SplitData.node0934 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0935
  · rfl

def B0933 : Block := .branch 163 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B0934]
theorem treeEq0933 : B0933.tree = HexagonCover.NBand.M8300_8500.SplitData.node0933 := by
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
  · exact treeEq0934

def B0932 : Block := .branch 165 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B0933, (.leaf 0 [] 0)]
theorem treeEq0932 : B0932.tree = HexagonCover.NBand.M8300_8500.SplitData.node0932 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0933
  · rfl

def B0931 : Block := .branch 167 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 79237833920821254626941624328, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B0932, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq0931 : B0931.tree = HexagonCover.NBand.M8300_8500.SplitData.node0931 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0932
  · rfl

def B0927 : Block := .branch 119 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B0928, B0931, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq0927 : B0927.tree = HexagonCover.NBand.M8300_8500.SplitData.node0927 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0928
  · exact treeEq0931
  · rfl
  · rfl

def B0917 : Block := .branch 115 ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B0918, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B0927, (.leaf 0 [] 0)]
theorem treeEq0917 : B0917.tree = HexagonCover.NBand.M8300_8500.SplitData.node0917 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0918
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0927
  · rfl

theorem accepted0917 : B0917.accepted = true := by decide +kernel
theorem checked0917 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0917 (maskNeeds ![604463488519866704462209, 151152620940525821756930, 4873482210321473860540420, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq0917]
  exact B0917.sound accepted0917
#print axioms checked0917

end HexagonCover.NBand.M8300_8500.SplitTree.Run0011
