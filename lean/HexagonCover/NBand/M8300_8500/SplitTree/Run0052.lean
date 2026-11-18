import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0051
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0052
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip3666_3669 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3669 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0051.checked3669
def B3796 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 891).pointIds 891)]
theorem treeEq3796 : B3796.tree = HexagonCover.NBand.M8300_8500.SplitData.node3796 := by
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

def B3795 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783560772922806602663286214498992273986420800] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3796, (.leaf 6 (Common.fact 890).pointIds 890)]
theorem treeEq3795 : B3795.tree = HexagonCover.NBand.M8300_8500.SplitData.node3795 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3796
  · rfl

def B3794 : Block := .branch 138 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B3795, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3794 : B3794.tree = HexagonCover.NBand.M8300_8500.SplitData.node3794 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3795
  · rfl
  · rfl

def B3793 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B3794, (.leaf 0 [] 0)]
theorem treeEq3793 : B3793.tree = HexagonCover.NBand.M8300_8500.SplitData.node3793 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3794
  · rfl

def B3792 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B3793, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3792 : B3792.tree = HexagonCover.NBand.M8300_8500.SplitData.node3792 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3793
  · rfl

def B3791 : Block := .branch 146 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B3792, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3791 : B3791.tree = HexagonCover.NBand.M8300_8500.SplitData.node3791 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3792
  · rfl
  · rfl

def B3790 : Block := .branch 88 ![2251799813685633, 972778069267842562, 2923003274661805836407374538914776360785725626372, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 577).pointIds 577), B3791, (.leaf 2 (Common.fact 578).pointIds 578), (.leaf 3 (Common.fact 579).pointIds 579), (.leaf 4 (Common.fact 580).pointIds 580), (.leaf 5 (Common.fact 581).pointIds 581), (.leaf 6 (Common.fact 987).pointIds 987)]
theorem treeEq3790 : B3790.tree = HexagonCover.NBand.M8300_8500.SplitData.node3790 := by
  change Tree.branch (88 : Fin 177) _ = Tree.branch (88 : Fin 177) _
  apply congrArg (Tree.branch (88 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq3791
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B3789 : Block := .branch 161 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B3790, (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 967).pointIds 967)]
theorem treeEq3789 : B3789.tree = HexagonCover.NBand.M8300_8500.SplitData.node3789 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3790
  · rfl
  · rfl
  · rfl
  · rfl

def B3788 : Block := .branch 170 ![2251799813685633, 972778069267842562, 4873482210321473860540420, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849458423265328550009112758845504] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3789, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 858).pointIds 858)]
theorem treeEq3788 : B3788.tree = HexagonCover.NBand.M8300_8500.SplitData.node3788 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3789
  · rfl
  · rfl
  · rfl

def B3668 : Block := .branch 90 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip3666_3669, (.leaf 1 (Common.fact 192).pointIds 192), (.leaf 2 (Common.fact 193).pointIds 193), (.leaf 3 (Common.fact 194).pointIds 194), (.leaf 4 (Common.fact 195).pointIds 195), (.leaf 5 (Common.fact 196).pointIds 196), B3788]
theorem treeEq3668 : B3668.tree = HexagonCover.NBand.M8300_8500.SplitData.node3668 := by
  change Tree.branch (90 : Fin 177) _ = Tree.branch (90 : Fin 177) _
  apply congrArg (Tree.branch (90 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3788

def B3799 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3799 : B3799.tree = HexagonCover.NBand.M8300_8500.SplitData.node3799 := by
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

def B3798 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3799, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3798 : B3798.tree = HexagonCover.NBand.M8300_8500.SplitData.node3798 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3799
  · rfl

def B3797 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79305533766719673860725170184, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3798]
theorem treeEq3797 : B3797.tree = HexagonCover.NBand.M8300_8500.SplitData.node3797 := by
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
  · exact treeEq3798

def B3667 : Block := .branch 86 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B3668, B3797, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq3667 : B3667.tree = HexagonCover.NBand.M8300_8500.SplitData.node3667 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3668
  · exact treeEq3797
  · rfl
  · rfl
  · rfl

def B3802 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3802 : B3802.tree = HexagonCover.NBand.M8300_8500.SplitData.node3802 := by
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

def B3801 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3802, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3801 : B3801.tree = HexagonCover.NBand.M8300_8500.SplitData.node3801 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3802
  · rfl

def B3800 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 237723173169020680914222473224, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 968).pointIds 968), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3801]
theorem treeEq3800 : B3800.tree = HexagonCover.NBand.M8300_8500.SplitData.node3800 := by
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
  · exact treeEq3801

def B3666 : Block := .branch 85 ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B3667, B3800, (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq3666 : B3666.tree = HexagonCover.NBand.M8300_8500.SplitData.node3666 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq3667
  · exact treeEq3800
  · rfl
  · rfl
  · rfl

theorem accepted3666 : B3666.accepted = true := by decide +kernel
theorem checked3666 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3666 (maskNeeds ![2251799813685633, 1116893257343698434, 4873482210321473860540420, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq3666]
  exact B3666.sound accepted3666
#print axioms checked3666

def B3818 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 540).pointIds 540), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3818 : B3818.tree = HexagonCover.NBand.M8300_8500.SplitData.node3818 := by
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

def B3817 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3818, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3817 : B3817.tree = HexagonCover.NBand.M8300_8500.SplitData.node3817 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3818
  · rfl

def B3816 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3817]
theorem treeEq3816 : B3816.tree = HexagonCover.NBand.M8300_8500.SplitData.node3816 := by
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
  · exact treeEq3817

def B3823 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3823 : B3823.tree = HexagonCover.NBand.M8300_8500.SplitData.node3823 := by
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

def B3822 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3823, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3822 : B3822.tree = HexagonCover.NBand.M8300_8500.SplitData.node3822 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3823
  · rfl

def B3821 : Block := .branch 163 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B3822]
theorem treeEq3821 : B3821.tree = HexagonCover.NBand.M8300_8500.SplitData.node3821 := by
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
  · exact treeEq3822

def B3820 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B3821, (.leaf 0 [] 0)]
theorem treeEq3820 : B3820.tree = HexagonCover.NBand.M8300_8500.SplitData.node3820 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3821
  · rfl

def B3819 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B3820, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3819 : B3819.tree = HexagonCover.NBand.M8300_8500.SplitData.node3819 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3820
  · rfl

def B3815 : Block := .branch 119 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B3816, B3819, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3815 : B3815.tree = HexagonCover.NBand.M8300_8500.SplitData.node3815 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3816
  · exact treeEq3819
  · rfl
  · rfl

def B3827 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 748288838313422335658661502629357934307808096157728, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 618).pointIds 618), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq3827 : B3827.tree = HexagonCover.NBand.M8300_8500.SplitData.node3827 := by
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

def B3826 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 4863877460187617511047174694047649025739674011304000] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3827, (.leaf 6 (Common.fact 651).pointIds 651)]
theorem treeEq3826 : B3826.tree = HexagonCover.NBand.M8300_8500.SplitData.node3826 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3827
  · rfl

def B3825 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 664614394042941914330508531257597960, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), (.leaf 3 (Common.fact 849).pointIds 849), (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), B3826]
theorem treeEq3825 : B3825.tree = HexagonCover.NBand.M8300_8500.SplitData.node3825 := by
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
  · exact treeEq3826

def B3832 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3832 : B3832.tree = HexagonCover.NBand.M8300_8500.SplitData.node3832 := by
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

def B3831 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3832, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3831 : B3831.tree = HexagonCover.NBand.M8300_8500.SplitData.node3831 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3832
  · rfl

def B3830 : Block := .branch 163 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B3831]
theorem treeEq3830 : B3830.tree = HexagonCover.NBand.M8300_8500.SplitData.node3830 := by
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
  · exact treeEq3831

def B3829 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B3830, (.leaf 0 [] 0)]
theorem treeEq3829 : B3829.tree = HexagonCover.NBand.M8300_8500.SplitData.node3829 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3830
  · rfl

def B3828 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B3829, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3828 : B3828.tree = HexagonCover.NBand.M8300_8500.SplitData.node3828 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3829
  · rfl

def B3824 : Block := .branch 119 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B3825, B3828, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3824 : B3824.tree = HexagonCover.NBand.M8300_8500.SplitData.node3824 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3825
  · exact treeEq3828
  · rfl
  · rfl

def B3814 : Block := .branch 115 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B3815, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B3824, (.leaf 0 [] 0)]
theorem treeEq3814 : B3814.tree = HexagonCover.NBand.M8300_8500.SplitData.node3814 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq3815
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3824
  · rfl

theorem accepted3814 : B3814.accepted = true := by decide +kernel
theorem checked3814 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3814 (maskNeeds ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq3814]
  exact B3814.sound accepted3814
#print axioms checked3814

def Tip3812_3814 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3814 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked3814
def B3842 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 663).pointIds 663)]
theorem treeEq3842 : B3842.tree = HexagonCover.NBand.M8300_8500.SplitData.node3842 := by
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
  · rfl

def B3841 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B3842, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3841 : B3841.tree = HexagonCover.NBand.M8300_8500.SplitData.node3841 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3842
  · rfl
  · rfl

def B3840 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606016441093407323855830516522741661760] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B3841, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq3840 : B3840.tree = HexagonCover.NBand.M8300_8500.SplitData.node3840 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3841
  · rfl
  · rfl

def B3839 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B3840, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3839 : B3839.tree = HexagonCover.NBand.M8300_8500.SplitData.node3839 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3840
  · rfl
  · rfl

def B3838 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B3839, (.leaf 0 [] 0)]
theorem treeEq3838 : B3838.tree = HexagonCover.NBand.M8300_8500.SplitData.node3838 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3839
  · rfl

def B3837 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B3838, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3837 : B3837.tree = HexagonCover.NBand.M8300_8500.SplitData.node3837 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3838
  · rfl

def B3836 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B3837, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3836 : B3836.tree = HexagonCover.NBand.M8300_8500.SplitData.node3836 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3837
  · rfl
  · rfl

def B3835 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 4115588610745627284089025965977822291429487227174976] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3836, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq3835 : B3835.tree = HexagonCover.NBand.M8300_8500.SplitData.node3835 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3836
  · rfl
  · rfl
  · rfl

def B3834 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204989968739331627085385365649765171264] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B3835]
theorem treeEq3834 : B3834.tree = HexagonCover.NBand.M8300_8500.SplitData.node3834 := by
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
  · exact treeEq3835

def B3833 : Block := .branch 135 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577589234050902394944521689830518161472] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B3834, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq3833 : B3833.tree = HexagonCover.NBand.M8300_8500.SplitData.node3833 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3834
  · rfl

def B3813 : Block := .branch 113 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip3812_3814, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B3833]
theorem treeEq3813 : B3813.tree = HexagonCover.NBand.M8300_8500.SplitData.node3813 := by
  change Tree.branch (113 : Fin 177) _ = Tree.branch (113 : Fin 177) _
  apply congrArg (Tree.branch (113 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3833

def B3847 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3847 : B3847.tree = HexagonCover.NBand.M8300_8500.SplitData.node3847 := by
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

def B3846 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3847, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3846 : B3846.tree = HexagonCover.NBand.M8300_8500.SplitData.node3846 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3847
  · rfl

def B3845 : Block := .branch 163 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B3846]
theorem treeEq3845 : B3845.tree = HexagonCover.NBand.M8300_8500.SplitData.node3845 := by
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
  · exact treeEq3846

def B3844 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B3845, (.leaf 0 [] 0)]
theorem treeEq3844 : B3844.tree = HexagonCover.NBand.M8300_8500.SplitData.node3844 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3845
  · rfl

def B3843 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B3844, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3843 : B3843.tree = HexagonCover.NBand.M8300_8500.SplitData.node3843 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3844
  · rfl

def B3812 : Block := .branch 108 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B3813, B3843, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq3812 : B3812.tree = HexagonCover.NBand.M8300_8500.SplitData.node3812 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3813
  · exact treeEq3843
  · rfl
  · rfl

theorem accepted3812 : B3812.accepted = true := by decide +kernel
theorem checked3812 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3812 (maskNeeds ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq3812]
  exact B3812.sound accepted3812
#print axioms checked3812

def Tip3810_3812 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node3812 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] checked3812
def B3857 : Block := .branch 163 ![385, 1538, 6148, 24584, 89202981459385527565917662996063288205344784, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 857).pointIds 857), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 761).pointIds 761)]
theorem treeEq3857 : B3857.tree = HexagonCover.NBand.M8300_8500.SplitData.node3857 := by
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
  · rfl

def B3856 : Block := .branch 119 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), (.leaf 3 (Common.fact 856).pointIds 856), B3857, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq3856 : B3856.tree = HexagonCover.NBand.M8300_8500.SplitData.node3856 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3857
  · rfl
  · rfl

def B3855 : Block := .branch 129 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745606006057767340854428802857026786426944] ![(.leaf 0 (Common.fact 262).pointIds 262), (.leaf 1 (Common.fact 263).pointIds 263), (.leaf 2 (Common.fact 264).pointIds 264), (.leaf 3 (Common.fact 854).pointIds 854), B3856, (.leaf 5 (Common.fact 265).pointIds 265), (.leaf 6 (Common.fact 855).pointIds 855)]
theorem treeEq3855 : B3855.tree = HexagonCover.NBand.M8300_8500.SplitData.node3855 := by
  change Tree.branch (129 : Fin 177) _ = Tree.branch (129 : Fin 177) _
  apply congrArg (Tree.branch (129 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3856
  · rfl
  · rfl

def B3854 : Block := .branch 138 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 853).pointIds 853), B3855, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq3854 : B3854.tree = HexagonCover.NBand.M8300_8500.SplitData.node3854 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3855
  · rfl
  · rfl

def B3853 : Block := .branch 165 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B3854, (.leaf 0 [] 0)]
theorem treeEq3853 : B3853.tree = HexagonCover.NBand.M8300_8500.SplitData.node3853 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3854
  · rfl

def B3852 : Block := .branch 167 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 89202980794771529673459726544159758065172496, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B3853, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3852 : B3852.tree = HexagonCover.NBand.M8300_8500.SplitData.node3852 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3853
  · rfl

def B3851 : Block := .branch 146 ![385, 1538, 6148, 1496577676626844588240573278372880369044708321681416, 649037107316853453566312041250832, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 852).pointIds 852), B3852, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq3851 : B3851.tree = HexagonCover.NBand.M8300_8500.SplitData.node3851 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3852
  · rfl
  · rfl

def B3850 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37778931862957161715716, 9671406556917033397673992, 178405961588894022239602599634753204089094160, 393248, 4115588610745627273705699899508395263769991271940160] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B3851, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq3850 : B3850.tree = HexagonCover.NBand.M8300_8500.SplitData.node3850 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3851
  · rfl
  · rfl
  · rfl

def B3849 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 43556142965880123323311949751266331459616, 3367299772432204979585413265157658357706153809936448] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B3850]
theorem treeEq3849 : B3849.tree = HexagonCover.NBand.M8300_8500.SplitData.node3849 := by
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
  · exact treeEq3850

def B3848 : Block := .branch 135 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578850724835925517494030334562926656] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B3849, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq3848 : B3848.tree = HexagonCover.NBand.M8300_8500.SplitData.node3848 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3849
  · rfl

def B3811 : Block := .branch 100 ![2251799813685633, 972778069267842562, 37778931862957161715716, 396150483977878605001117425672, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![Tip3810_3812, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B3848]
theorem treeEq3811 : B3811.tree = HexagonCover.NBand.M8300_8500.SplitData.node3811 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3848

def B3862 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq3862 : B3862.tree = HexagonCover.NBand.M8300_8500.SplitData.node3862 := by
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

def B3861 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B3862, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq3861 : B3861.tree = HexagonCover.NBand.M8300_8500.SplitData.node3861 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3862
  · rfl

def B3860 : Block := .branch 163 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 649).pointIds 649), (.leaf 5 (Common.fact 329).pointIds 329), B3861]
theorem treeEq3860 : B3860.tree = HexagonCover.NBand.M8300_8500.SplitData.node3860 := by
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
  · exact treeEq3861

def B3859 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 648).pointIds 648), B3860, (.leaf 0 [] 0)]
theorem treeEq3859 : B3859.tree = HexagonCover.NBand.M8300_8500.SplitData.node3859 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3860
  · rfl

def B3858 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796575557517966312892902957208811175952, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 647).pointIds 647), B3859, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq3858 : B3858.tree = HexagonCover.NBand.M8300_8500.SplitData.node3858 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq3859
  · rfl

def B3810 : Block := .branch 98 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B3811, B3858, (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 616).pointIds 616)]
theorem treeEq3810 : B3810.tree = HexagonCover.NBand.M8300_8500.SplitData.node3810 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq3811
  · exact treeEq3858
  · rfl
  · rfl

theorem accepted3810 : B3810.accepted = true := by decide +kernel
theorem checked3810 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node3810 (maskNeeds ![2251799813685633, 972778069267842562, 37778931862957161715716, 79237833920821254626941624328, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280]) := by
  rw [← treeEq3810]
  exact B3810.sound accepted3810
#print axioms checked3810

end HexagonCover.NBand.M8300_8500.SplitTree.Run0052
