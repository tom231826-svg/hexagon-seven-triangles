import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0013
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0014
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip0935_0954 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0954 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] HexagonCover.NBand.M6667_6700.SplitTree.Run0013.checked0954
def B0943 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0943 : B0943.tree = HexagonCover.NBand.M6667_6700.SplitData.node0943 := by
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

def B0942 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B0943]
theorem treeEq0942 : B0942.tree = HexagonCover.NBand.M6667_6700.SplitData.node0942 := by
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
  · exact treeEq0943

def B0945 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 1021).pointIds 1021)]
theorem treeEq0945 : B0945.tree = HexagonCover.NBand.M6667_6700.SplitData.node0945 := by
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

def B0944 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138763077005735620634406571455008595762479168] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B0945, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq0944 : B0944.tree = HexagonCover.NBand.M6667_6700.SplitData.node0944 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0945
  · rfl
  · rfl

def B0941 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B0942, (.leaf 5 (Common.fact 439).pointIds 439), B0944]
theorem treeEq0941 : B0941.tree = HexagonCover.NBand.M6667_6700.SplitData.node0941 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0942
  · rfl
  · exact treeEq0944

def B0947 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7120435977076159682102984222751781438368531596443712] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1019).pointIds 1019)]
theorem treeEq0947 : B0947.tree = HexagonCover.NBand.M6667_6700.SplitData.node0947 := by
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

def B0946 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6372147138762737387982697588401044532304694134440000] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B0947]
theorem treeEq0946 : B0946.tree = HexagonCover.NBand.M6667_6700.SplitData.node0946 := by
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
  · exact treeEq0947

def B0940 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762737389281088715684808496787692392546368] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B0941, B0946, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq0940 : B0940.tree = HexagonCover.NBand.M6667_6700.SplitData.node0940 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0941
  · exact treeEq0946
  · rfl
  · rfl

def B0950 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9365302492016425899849846233346055704656513842282560] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 1020).pointIds 1020)]
theorem treeEq0950 : B0950.tree = HexagonCover.NBand.M6667_6700.SplitData.node0950 := by
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

def B0949 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6372147138762736723368699695943108080401163994267712] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B0950]
theorem treeEq0949 : B0949.tree = HexagonCover.NBand.M6667_6700.SplitData.node0949 := by
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
  · exact treeEq0950

def B0948 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6372147138762736724991292464235241714316944097148992] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B0949, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq0948 : B0948.tree = HexagonCover.NBand.M6667_6700.SplitData.node0948 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0949
  · rfl
  · rfl

def B0939 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0940, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B0948, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq0939 : B0939.tree = HexagonCover.NBand.M6667_6700.SplitData.node0939 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0940
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0948
  · rfl

def B0953 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq0953 : B0953.tree = HexagonCover.NBand.M6667_6700.SplitData.node0953 := by
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

def B0952 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B0953]
theorem treeEq0952 : B0952.tree = HexagonCover.NBand.M6667_6700.SplitData.node0952 := by
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
  · exact treeEq0953

def B0951 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B0952, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq0951 : B0951.tree = HexagonCover.NBand.M6667_6700.SplitData.node0951 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0952
  · rfl
  · rfl

def B0938 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762737389605607269343235223570848413122624] ![B0939, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B0951]
theorem treeEq0938 : B0938.tree = HexagonCover.NBand.M6667_6700.SplitData.node0938 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0939
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0951

def B0937 : Block := .branch 72 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B0938, Tip0935_0954, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1015).pointIds 1015)]
theorem treeEq0937 : B0937.tree = HexagonCover.NBand.M6667_6700.SplitData.node0937 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0938
  · rfl
  · rfl
  · rfl
  · rfl

def B0936 : Block := .branch 140 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6372147138762740048061598839174981031184968973811776] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B0937, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq0936 : B0936.tree = HexagonCover.NBand.M6667_6700.SplitData.node0936 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0937
  · rfl
  · rfl

def B0935 : Block := .branch 163 ![5319508131568930906582414993892835713, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![(.leaf 0 (Common.fact 526).pointIds 526), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B0936]
theorem treeEq0935 : B0935.tree = HexagonCover.NBand.M6667_6700.SplitData.node0935 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0936

theorem accepted0935 : B0935.accepted = true := by decide +kernel
theorem checked0935 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0935 (maskNeeds ![5319508131568930906582414993892835713, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq0935]
  exact B0935.sound accepted0935
#print axioms checked0935

def Tip0934_1022 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node1022 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] HexagonCover.NBand.M6667_6700.SplitTree.Run0013.checked1022
def Tip0934_0935 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node0935 ![5319508131568930906582414993892835713, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] checked0935
def B1011 : Block := .branch 132 ![385, 1538, 6148, 24584, 1394136857275084884809445766647954362433552, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 534).pointIds 534), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1011 : B1011.tree = HexagonCover.NBand.M6667_6700.SplitData.node1011 := by
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

def B1010 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1394136857275084884809445766647954362433552, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 533).pointIds 533), (.leaf 5 (Common.fact 371).pointIds 371), B1011]
theorem treeEq1010 : B1010.tree = HexagonCover.NBand.M6667_6700.SplitData.node1010 := by
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
  · exact treeEq1011

def B1013 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq1013 : B1013.tree = HexagonCover.NBand.M6667_6700.SplitData.node1013 := by
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

def B1012 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664435099301974295408332806079589423513664] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1013, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq1012 : B1012.tree = HexagonCover.NBand.M6667_6700.SplitData.node1012 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1013
  · rfl
  · rfl

def B1009 : Block := .branch 128 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), B1010, (.leaf 5 (Common.fact 439).pointIds 439), B1012]
theorem treeEq1009 : B1009.tree = HexagonCover.NBand.M6667_6700.SplitData.node1009 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1010
  · rfl
  · exact treeEq1012

def B1015 : Block := .branch 132 ![385, 1538, 6148, 24584, 1393966716091624415577714079344238478327824, 393248, 7108743963977517775669337883753542789439525257478208] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 638).pointIds 638), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq1015 : B1015.tree = HexagonCover.NBand.M6667_6700.SplitData.node1015 := by
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

def B1014 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 1393966716091624415577714079344238478327824, 393248, 6360455125664095481549051249402805883375687795474496] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 637).pointIds 637), (.leaf 5 (Common.fact 371).pointIds 371), B1015]
theorem treeEq1014 : B1014.tree = HexagonCover.NBand.M6667_6700.SplitData.node1014 := by
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
  · exact treeEq1015

def B1008 : Block := .branch 127 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664095482847442376686569847858686053580864] ![(.leaf 0 (Common.fact 477).pointIds 477), (.leaf 1 (Common.fact 478).pointIds 478), (.leaf 2 (Common.fact 479).pointIds 479), B1009, B1014, (.leaf 5 (Common.fact 481).pointIds 481), (.leaf 6 (Common.fact 1017).pointIds 1017)]
theorem treeEq1008 : B1008.tree = HexagonCover.NBand.M6667_6700.SplitData.node1008 := by
  change Tree.branch (127 : Fin 173) _ = Tree.branch (127 : Fin 173) _
  apply congrArg (Tree.branch (127 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq1009
  · exact treeEq1014
  · rfl
  · rfl

def B1018 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 9353610478917783993416199894347817055727507503317056] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 935).pointIds 935), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 634).pointIds 634)]
theorem treeEq1018 : B1018.tree = HexagonCover.NBand.M6667_6700.SplitData.node1018 := by
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

def B1017 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 187072211494825864028797084813410015571677932519440, 393248, 6360455125664094816935053356944869431472157655302208] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 934).pointIds 934), (.leaf 5 (Common.fact 909).pointIds 909), B1018]
theorem treeEq1017 : B1017.tree = HexagonCover.NBand.M6667_6700.SplitData.node1017 := by
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
  · exact treeEq1018

def B1016 : Block := .branch 167 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 42535295865117307932921825928971419680, 6360455125664094818557646125237003065387937758183488] ![(.leaf 0 (Common.fact 1007).pointIds 1007), (.leaf 1 (Common.fact 877).pointIds 877), (.leaf 2 (Common.fact 1008).pointIds 1008), (.leaf 3 (Common.fact 1009).pointIds 1009), B1017, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 1022).pointIds 1022)]
theorem treeEq1016 : B1016.tree = HexagonCover.NBand.M6667_6700.SplitData.node1016 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1017
  · rfl
  · rfl

def B1007 : Block := .branch 125 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B1008, (.leaf 1 (Common.fact 185).pointIds 185), (.leaf 2 (Common.fact 186).pointIds 186), (.leaf 3 (Common.fact 187).pointIds 187), (.leaf 4 (Common.fact 188).pointIds 188), B1016, (.leaf 6 (Common.fact 1016).pointIds 1016)]
theorem treeEq1007 : B1007.tree = HexagonCover.NBand.M6667_6700.SplitData.node1007 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1008
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1016
  · rfl

def B1021 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1021 : B1021.tree = HexagonCover.NBand.M6667_6700.SplitData.node1021 := by
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

def B1020 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1021]
theorem treeEq1020 : B1020.tree = HexagonCover.NBand.M6667_6700.SplitData.node1020 := by
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
  · exact treeEq1021

def B1019 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1020, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1019 : B1019.tree = HexagonCover.NBand.M6667_6700.SplitData.node1019 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1020
  · rfl
  · rfl

def B1006 : Block := .branch 123 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664095483171960930344996574641842074157120] ![B1007, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1019]
theorem treeEq1006 : B1006.tree = HexagonCover.NBand.M6667_6700.SplitData.node1006 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1007
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1019

def B1005 : Block := .branch 72 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1916470290498725426225725789055718567018512, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B1006, Tip0934_1022, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1025).pointIds 1025)]
theorem treeEq1005 : B1005.tree = HexagonCover.NBand.M6667_6700.SplitData.node1005 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1006
  · rfl
  · rfl
  · rfl
  · rfl

def B1004 : Block := .branch 140 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664098141627952500176742382255962634846272] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B1005, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 675).pointIds 675)]
theorem treeEq1004 : B1004.tree = HexagonCover.NBand.M6667_6700.SplitData.node1004 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1005
  · rfl
  · rfl

def B0934 : Block := .branch 122 ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968] ![Tip0934_0935, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), B1004]
theorem treeEq0934 : B0934.tree = HexagonCover.NBand.M6667_6700.SplitData.node0934 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1004

theorem accepted0934 : B0934.accepted = true := by decide +kernel
theorem checked0934 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node0934 (maskNeeds ![2596148429267414967186752771457409, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 522673715590561479879743397015195972894736, 393248, 6360455125664092824715969360513250767027721513467968]) := by
  rw [← treeEq0934]
  exact B0934.sound accepted0934
#print axioms checked0934

def B1076 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1076 : B1076.tree = HexagonCover.NBand.M6667_6700.SplitData.node1076 := by
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

def B1075 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1076]
theorem treeEq1075 : B1075.tree = HexagonCover.NBand.M6667_6700.SplitData.node1075 := by
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
  · exact treeEq1076

def B1079 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1079 : B1079.tree = HexagonCover.NBand.M6667_6700.SplitData.node1079 := by
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

def B1078 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1079]
theorem treeEq1078 : B1078.tree = HexagonCover.NBand.M6667_6700.SplitData.node1078 := by
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
  · exact treeEq1079

def B1077 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1078, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1077 : B1077.tree = HexagonCover.NBand.M6667_6700.SplitData.node1077 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1078
  · rfl
  · rfl

def B1074 : Block := .branch 119 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1075, (.leaf 5 (Common.fact 419).pointIds 419), B1077]
theorem treeEq1074 : B1074.tree = HexagonCover.NBand.M6667_6700.SplitData.node1074 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1075
  · rfl
  · exact treeEq1077

def B1081 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1081 : B1081.tree = HexagonCover.NBand.M6667_6700.SplitData.node1081 := by
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

def B1080 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1081, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1080 : B1080.tree = HexagonCover.NBand.M6667_6700.SplitData.node1080 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1081
  · rfl
  · rfl

def B1073 : Block := .branch 112 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1074, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1080]
theorem treeEq1073 : B1073.tree = HexagonCover.NBand.M6667_6700.SplitData.node1073 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1074
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1080

def B1085 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511797063390009257841148655409829511232] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq1085 : B1085.tree = HexagonCover.NBand.M6667_6700.SplitData.node1085 := by
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

def B1084 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 2361183241434822631432, 664613997892457936451903530140270608, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B1085]
theorem treeEq1084 : B1084.tree = HexagonCover.NBand.M6667_6700.SplitData.node1084 := by
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
  · exact treeEq1085

def B1088 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917778679099731358651625140063766194946112] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq1088 : B1088.tree = HexagonCover.NBand.M6667_6700.SplitData.node1088 := by
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

def B1087 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664089502618584821248677515808416346931264] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1088]
theorem treeEq1087 : B1087.tree = HexagonCover.NBand.M6667_6700.SplitData.node1087 := by
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
  · exact treeEq1088

def B1086 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664090167232582713706613967711946487103552] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1087, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 655).pointIds 655)]
theorem treeEq1086 : B1086.tree = HexagonCover.NBand.M6667_6700.SplitData.node1086 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1087
  · rfl
  · rfl

def B1083 : Block := .branch 119 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B1084, (.leaf 5 (Common.fact 419).pointIds 419), B1086]
theorem treeEq1083 : B1083.tree = HexagonCover.NBand.M6667_6700.SplitData.node1083 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1084
  · rfl
  · exact treeEq1086

def B1090 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 659).pointIds 659), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 660).pointIds 660)]
theorem treeEq1090 : B1090.tree = HexagonCover.NBand.M6667_6700.SplitData.node1090 := by
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

def B1089 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089505539251804174518056856820532117568] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1090, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 658).pointIds 658)]
theorem treeEq1089 : B1089.tree = HexagonCover.NBand.M6667_6700.SplitData.node1089 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1090
  · rfl
  · rfl

def B1082 : Block := .branch 112 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![B1083, (.leaf 1 (Common.fact 649).pointIds 649), (.leaf 2 (Common.fact 650).pointIds 650), (.leaf 3 (Common.fact 651).pointIds 651), (.leaf 4 (Common.fact 652).pointIds 652), (.leaf 5 (Common.fact 653).pointIds 653), B1089]
theorem treeEq1082 : B1082.tree = HexagonCover.NBand.M6667_6700.SplitData.node1082 := by
  change Tree.branch (112 : Fin 173) _ = Tree.branch (112 : Fin 173) _
  apply congrArg (Tree.branch (112 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1083
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1089

def B1072 : Block := .branch 72 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] ![(.leaf 0 (Common.fact 911).pointIds 911), (.leaf 1 (Common.fact 912).pointIds 912), B1073, B1082, (.leaf 4 (Common.fact 913).pointIds 913), (.leaf 5 (Common.fact 914).pointIds 914), (.leaf 6 (Common.fact 1028).pointIds 1028)]
theorem treeEq1072 : B1072.tree = HexagonCover.NBand.M6667_6700.SplitData.node1072 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1073
  · exact treeEq1082
  · rfl
  · rfl
  · rfl

theorem accepted1072 : B1072.accepted = true := by decide +kernel
theorem checked1072 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1072 (maskNeeds ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520]) := by
  rw [← treeEq1072]
  exact B1072.sound accepted1072
#print axioms checked1072

def B1128 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1128 : B1128.tree = HexagonCover.NBand.M6667_6700.SplitData.node1128 := by
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

def B1127 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1128, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1127 : B1127.tree = HexagonCover.NBand.M6667_6700.SplitData.node1127 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1128
  · rfl
  · rfl

def B1126 : Block := .branch 158 ![10636420114708594398197643235014214017, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1127]
theorem treeEq1126 : B1126.tree = HexagonCover.NBand.M6667_6700.SplitData.node1126 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1127

def B1131 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1131 : B1131.tree = HexagonCover.NBand.M6667_6700.SplitData.node1131 := by
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

def B1130 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1131]
theorem treeEq1130 : B1130.tree = HexagonCover.NBand.M6667_6700.SplitData.node1130 := by
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
  · exact treeEq1131

def B1129 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1130, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1129 : B1129.tree = HexagonCover.NBand.M6667_6700.SplitData.node1129 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1130
  · rfl
  · rfl

def B1125 : Block := .branch 123 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1126, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1129]
theorem treeEq1125 : B1125.tree = HexagonCover.NBand.M6667_6700.SplitData.node1125 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1126
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1129

def B1135 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 677).pointIds 677)]
theorem treeEq1135 : B1135.tree = HexagonCover.NBand.M6667_6700.SplitData.node1135 := by
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

def B1134 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915142616647043973987696704] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), B1135, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 676).pointIds 676)]
theorem treeEq1134 : B1134.tree = HexagonCover.NBand.M6667_6700.SplitData.node1134 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1135
  · rfl
  · rfl

def B1133 : Block := .branch 158 ![10636420114708594398197643235014214017, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![(.leaf 0 (Common.fact 218).pointIds 218), (.leaf 1 (Common.fact 672).pointIds 672), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B1134]
theorem treeEq1133 : B1133.tree = HexagonCover.NBand.M6667_6700.SplitData.node1133 := by
  change Tree.branch (158 : Fin 173) _ = Tree.branch (158 : Fin 173) _
  apply congrArg (Tree.branch (158 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1134

def B1138 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208711194556255000273092672] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 640).pointIds 640)]
theorem treeEq1138 : B1138.tree = HexagonCover.NBand.M6667_6700.SplitData.node1138 := by
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

def B1137 : Block := .branch 171 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671308246931999650425077824] ![(.leaf 0 (Common.fact 1012).pointIds 1012), (.leaf 1 (Common.fact 865).pointIds 865), (.leaf 2 (Common.fact 1013).pointIds 1013), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B1138]
theorem treeEq1137 : B1137.tree = HexagonCover.NBand.M6667_6700.SplitData.node1137 := by
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
  · exact treeEq1138

def B1136 : Block := .branch 169 ![1152921504606847361, 147573953689188042242, 36893488147419109380, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563766183383903180565250112] ![(.leaf 0 (Common.fact 999).pointIds 999), (.leaf 1 (Common.fact 868).pointIds 868), (.leaf 2 (Common.fact 1000).pointIds 1000), (.leaf 3 (Common.fact 1001).pointIds 1001), B1137, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 639).pointIds 639)]
theorem treeEq1136 : B1136.tree = HexagonCover.NBand.M6667_6700.SplitData.node1136 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1137
  · rfl
  · rfl

def B1132 : Block := .branch 123 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408993934437576289060004560960] ![B1133, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B1136]
theorem treeEq1132 : B1132.tree = HexagonCover.NBand.M6667_6700.SplitData.node1132 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq1133
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq1136

def B1124 : Block := .branch 74 ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B1125, B1132, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 1027).pointIds 1027)]
theorem treeEq1124 : B1124.tree = HexagonCover.NBand.M6667_6700.SplitData.node1124 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq1125
  · exact treeEq1132
  · rfl
  · rfl
  · rfl

theorem accepted1124 : B1124.accepted = true := by decide +kernel
theorem checked1124 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node1124 (maskNeeds ![2596148429267414967186752771457409, 618970757512454185343256066, 36893488147419109380, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819234551690989808356163648]) := by
  rw [← treeEq1124]
  exact B1124.sound accepted1124
#print axioms checked1124

end HexagonCover.NBand.M6667_6700.SplitTree.Run0014
