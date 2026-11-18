import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.NBand.M8300_8500.SplitTree.Run0056
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0057
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def Tip2378_2386 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node2386 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] HexagonCover.NBand.M8300_8500.SplitTree.Run0056.checked2386
def B4106 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 692).pointIds 692)]
theorem treeEq4106 : B4106.tree = HexagonCover.NBand.M8300_8500.SplitData.node4106 := by
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

def B4105 : Block := .branch 169 ![2251799813685633, 972778069267842562, 37778931862957161715716, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 984).pointIds 984), (.leaf 2 (Common.fact 870).pointIds 870), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4106, (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq4105 : B4105.tree = HexagonCover.NBand.M8300_8500.SplitData.node4105 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4106
  · rfl

def B4104 : Block := .branch 84 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 182).pointIds 182), (.leaf 1 (Common.fact 183).pointIds 183), B4105, (.leaf 3 (Common.fact 976).pointIds 976), (.leaf 4 (Common.fact 184).pointIds 184), (.leaf 5 (Common.fact 185).pointIds 185), (.leaf 6 (Common.fact 186).pointIds 186)]
theorem treeEq4104 : B4104.tree = HexagonCover.NBand.M8300_8500.SplitData.node4104 := by
  change Tree.branch (84 : Fin 177) _ = Tree.branch (84 : Fin 177) _
  apply congrArg (Tree.branch (84 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4105
  · rfl
  · rfl
  · rfl
  · rfl

def B4103 : Block := .branch 85 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 187).pointIds 187), (.leaf 1 (Common.fact 188).pointIds 188), B4104, (.leaf 3 (Common.fact 818).pointIds 818), (.leaf 4 (Common.fact 189).pointIds 189), (.leaf 5 (Common.fact 190).pointIds 190), (.leaf 6 (Common.fact 191).pointIds 191)]
theorem treeEq4103 : B4103.tree = HexagonCover.NBand.M8300_8500.SplitData.node4103 := by
  change Tree.branch (85 : Fin 177) _ = Tree.branch (85 : Fin 177) _
  apply congrArg (Tree.branch (85 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4104
  · rfl
  · rfl
  · rfl
  · rfl

def B4102 : Block := .branch 86 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966198037638581774101091462480179458736192] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B4103, (.leaf 3 (Common.fact 650).pointIds 650), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 845).pointIds 845)]
theorem treeEq4102 : B4102.tree = HexagonCover.NBand.M8300_8500.SplitData.node4102 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4103
  · rfl
  · rfl
  · rfl
  · rfl

def B4101 : Block := .branch 138 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 277).pointIds 277), (.leaf 1 (Common.fact 278).pointIds 278), (.leaf 2 (Common.fact 279).pointIds 279), (.leaf 3 (Common.fact 662).pointIds 662), B4102, (.leaf 5 (Common.fact 280).pointIds 280), (.leaf 6 (Common.fact 281).pointIds 281)]
theorem treeEq4101 : B4101.tree = HexagonCover.NBand.M8300_8500.SplitData.node4101 := by
  change Tree.branch (138 : Fin 177) _ = Tree.branch (138 : Fin 177) _
  apply congrArg (Tree.branch (138 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4102
  · rfl
  · rfl

def B4100 : Block := .branch 165 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 187072209578355573530071658587684226515959365894176, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 593).pointIds 593), B4101, (.leaf 0 [] 0)]
theorem treeEq4100 : B4100.tree = HexagonCover.NBand.M8300_8500.SplitData.node4100 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4101
  · rfl

def B4099 : Block := .branch 167 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 90596777369679693619805708936200280659296272, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 592).pointIds 592), B4100, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4099 : B4099.tree = HexagonCover.NBand.M8300_8500.SplitData.node4099 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4100
  · rfl

def B4098 : Block := .branch 146 ![2251799813685633, 972778069267842562, 37778931862957161715716, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 292).pointIds 292), (.leaf 1 (Common.fact 293).pointIds 293), (.leaf 2 (Common.fact 294).pointIds 294), (.leaf 3 (Common.fact 661).pointIds 661), B4099, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 0 [] 0)]
theorem treeEq4098 : B4098.tree = HexagonCover.NBand.M8300_8500.SplitData.node4098 := by
  change Tree.branch (146 : Fin 177) _ = Tree.branch (146 : Fin 177) _
  apply congrArg (Tree.branch (146 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4099
  · rfl
  · rfl

def B4097 : Block := .branch 161 ![2251799813685633, 972778069267842562, 37815825351104580818948, 1496577676626844588240652496863988076465268467982344, 1393796575557201053662835845606834635374608, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 966).pointIds 966), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4098]
theorem treeEq4097 : B4097.tree = HexagonCover.NBand.M8300_8500.SplitData.node4097 := by
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
  · exact treeEq4098

def B4096 : Block := .branch 170 ![2251799813685633, 972778069267842562, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 375605931966219305286514332755057923393143944249408] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 986).pointIds 986), (.leaf 2 (Common.fact 872).pointIds 872), B4097, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 691).pointIds 691)]
theorem treeEq4096 : B4096.tree = HexagonCover.NBand.M8300_8500.SplitData.node4096 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4097
  · rfl
  · rfl
  · rfl

def B4095 : Block := .branch 160 ![2251799813685633, 972778069267842562, 37815825351104580818948, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 347).pointIds 347), (.leaf 1 (Common.fact 988).pointIds 988), (.leaf 2 (Common.fact 975).pointIds 975), (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B4096]
theorem treeEq4095 : B4095.tree = HexagonCover.NBand.M8300_8500.SplitData.node4095 := by
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
  · exact treeEq4096

def B2385 : Block := .branch 65 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163802186185948582026793726683217936, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 143).pointIds 143), Tip2378_2386, B4095, (.leaf 3 (Common.fact 144).pointIds 144), (.leaf 4 (Common.fact 145).pointIds 145), (.leaf 5 (Common.fact 146).pointIds 146), (.leaf 6 (Common.fact 147).pointIds 147)]
theorem treeEq2385 : B2385.tree = HexagonCover.NBand.M8300_8500.SplitData.node2385 := by
  change Tree.branch (65 : Fin 177) _ = Tree.branch (65 : Fin 177) _
  apply congrArg (Tree.branch (65 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq4095
  · rfl
  · rfl
  · rfl
  · rfl

def B2384 : Block := .branch 109 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 3367299783582577578849457185325289264628837859721280] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B2385, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 6 (Common.fact 841).pointIds 841)]
theorem treeEq2384 : B2384.tree = HexagonCover.NBand.M8300_8500.SplitData.node2384 := by
  change Tree.branch (109 : Fin 177) _ = Tree.branch (109 : Fin 177) _
  apply congrArg (Tree.branch (109 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2385
  · rfl
  · rfl

def B2383 : Block := .branch 171 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 981).pointIds 981), (.leaf 1 (Common.fact 982).pointIds 982), (.leaf 2 (Common.fact 868).pointIds 868), (.leaf 3 (Common.fact 958).pointIds 958), (.leaf 4 (Common.fact 718).pointIds 718), (.leaf 5 (Common.fact 563).pointIds 563), B2384]
theorem treeEq2383 : B2383.tree = HexagonCover.NBand.M8300_8500.SplitData.node2383 := by
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
  · exact treeEq2384

def B2382 : Block := .branch 77 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 163).pointIds 163), B2383, (.leaf 2 (Common.fact 164).pointIds 164), (.leaf 3 (Common.fact 165).pointIds 165), (.leaf 4 (Common.fact 166).pointIds 166), (.leaf 5 (Common.fact 167).pointIds 167), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2382 : B2382.tree = HexagonCover.NBand.M8300_8500.SplitData.node2382 := by
  change Tree.branch (77 : Fin 177) _ = Tree.branch (77 : Fin 177) _
  apply congrArg (Tree.branch (77 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2383
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2381 : Block := .branch 79 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 237684487542793012780631875592, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B2382, (.leaf 1 (Common.fact 168).pointIds 168), (.leaf 2 (Common.fact 169).pointIds 169), (.leaf 3 (Common.fact 170).pointIds 170), (.leaf 4 (Common.fact 171).pointIds 171), (.leaf 5 (Common.fact 172).pointIds 172), (.leaf 6 (Common.fact 953).pointIds 953)]
theorem treeEq2381 : B2381.tree = HexagonCover.NBand.M8300_8500.SplitData.node2381 := by
  change Tree.branch (79 : Fin 177) _ = Tree.branch (79 : Fin 177) _
  apply congrArg (Tree.branch (79 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2382
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2380 : Block := .branch 97 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 197).pointIds 197), (.leaf 1 (Common.fact 198).pointIds 198), (.leaf 2 (Common.fact 199).pointIds 199), B2381, (.leaf 4 (Common.fact 200).pointIds 200), (.leaf 5 (Common.fact 201).pointIds 201), (.leaf 6 (Common.fact 815).pointIds 815)]
theorem treeEq2380 : B2380.tree = HexagonCover.NBand.M8300_8500.SplitData.node2380 := by
  change Tree.branch (97 : Fin 177) _ = Tree.branch (97 : Fin 177) _
  apply congrArg (Tree.branch (97 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2381
  · rfl
  · rfl
  · rfl

def B2379 : Block := .branch 80 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 374144430328888402368310647922341640373488011706432] ![B2380, (.leaf 1 (Common.fact 947).pointIds 947), (.leaf 2 (Common.fact 948).pointIds 948), (.leaf 3 (Common.fact 949).pointIds 949), (.leaf 4 (Common.fact 950).pointIds 950), (.leaf 5 (Common.fact 951).pointIds 951), (.leaf 6 (Common.fact 952).pointIds 952)]
theorem treeEq2379 : B2379.tree = HexagonCover.NBand.M8300_8500.SplitData.node2379 := by
  change Tree.branch (80 : Fin 177) _ = Tree.branch (80 : Fin 177) _
  apply congrArg (Tree.branch (80 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq2380
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2378 : Block := .branch 107 ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432] ![(.leaf 0 (Common.fact 776).pointIds 776), (.leaf 1 (Common.fact 777).pointIds 777), (.leaf 2 (Common.fact 778).pointIds 778), B2379, (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 780).pointIds 780), (.leaf 6 (Common.fact 781).pointIds 781)]
theorem treeEq2378 : B2378.tree = HexagonCover.NBand.M8300_8500.SplitData.node2378 := by
  change Tree.branch (107 : Fin 177) _ = Tree.branch (107 : Fin 177) _
  apply congrArg (Tree.branch (107 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2379
  · rfl
  · rfl
  · rfl

theorem accepted2378 : B2378.accepted = true := by decide +kernel
theorem checked2378 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node2378 (maskNeeds ![2251799813685633, 1116893257343698434, 37778931862957161715716, 79228162514264337593543974920, 179799759492381144863547601477034474922410000, 393248, 374144430328888402368310647922341640373488011706432]) := by
  rw [← treeEq2378]
  exact B2378.sound accepted2378
#print axioms checked2378

def B4142 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4142 : B4142.tree = HexagonCover.NBand.M8300_8500.SplitData.node4142 := by
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
  · rfl

def B4141 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4142, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4141 : B4141.tree = HexagonCover.NBand.M8300_8500.SplitData.node4141 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4142
  · rfl
  · rfl
  · rfl

def B4140 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42535295865117307932921825928971419680, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 540).pointIds 540), B4141]
theorem treeEq4140 : B4140.tree = HexagonCover.NBand.M8300_8500.SplitData.node4140 := by
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
  · exact treeEq4141

def B4146 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556142965880123323311949751266331459616, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4146 : B4146.tree = HexagonCover.NBand.M8300_8500.SplitData.node4146 := by
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
  · rfl

def B4145 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 393248, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4146, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4145 : B4145.tree = HexagonCover.NBand.M8300_8500.SplitData.node4145 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4146
  · rfl

def B4144 : Block := .branch 161 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4145]
theorem treeEq4144 : B4144.tree = HexagonCover.NBand.M8300_8500.SplitData.node4144 := by
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
  · exact treeEq4145

def B4143 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4144, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4143 : B4143.tree = HexagonCover.NBand.M8300_8500.SplitData.node4143 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4144
  · rfl
  · rfl
  · rfl

def B4139 : Block := .branch 125 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4140, B4143]
theorem treeEq4139 : B4139.tree = HexagonCover.NBand.M8300_8500.SplitData.node4139 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4140
  · exact treeEq4143

def B4150 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4150 : B4150.tree = HexagonCover.NBand.M8300_8500.SplitData.node4150 := by
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
  · rfl

def B4149 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4150, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4149 : B4149.tree = HexagonCover.NBand.M8300_8500.SplitData.node4149 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4150
  · rfl
  · rfl
  · rfl

def B4148 : Block := .branch 135 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422294120286634350736906063837462396960, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 589).pointIds 589), B4149]
theorem treeEq4148 : B4148.tree = HexagonCover.NBand.M8300_8500.SplitData.node4148 := by
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
  · exact treeEq4149

def B4147 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4148, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4147 : B4147.tree = HexagonCover.NBand.M8300_8500.SplitData.node4147 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4148
  · rfl

def B4138 : Block := .branch 121 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4139, (.leaf 5 (Common.fact 256).pointIds 256), B4147]
theorem treeEq4138 : B4138.tree = HexagonCover.NBand.M8300_8500.SplitData.node4138 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4139
  · rfl
  · exact treeEq4147

def B4155 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4155 : B4155.tree = HexagonCover.NBand.M8300_8500.SplitData.node4155 := by
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

def B4154 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4155, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4154 : B4154.tree = HexagonCover.NBand.M8300_8500.SplitData.node4154 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4155
  · rfl

def B4153 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4154]
theorem treeEq4153 : B4153.tree = HexagonCover.NBand.M8300_8500.SplitData.node4153 := by
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
  · exact treeEq4154

def B4152 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4153, (.leaf 0 [] 0)]
theorem treeEq4152 : B4152.tree = HexagonCover.NBand.M8300_8500.SplitData.node4152 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4153
  · rfl

def B4151 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4152, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4151 : B4151.tree = HexagonCover.NBand.M8300_8500.SplitData.node4151 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4152
  · rfl

def B4137 : Block := .branch 119 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4138, B4151, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4137 : B4137.tree = HexagonCover.NBand.M8300_8500.SplitData.node4137 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4138
  · exact treeEq4151
  · rfl
  · rfl

theorem accepted4137 : B4137.accepted = true := by decide +kernel
theorem checked4137 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4137 (maskNeeds ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4137]
  exact B4137.sound accepted4137
#print axioms checked4137

def Tip4136_4137 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4137 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4137
def B4161 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 621).pointIds 621)]
theorem treeEq4161 : B4161.tree = HexagonCover.NBand.M8300_8500.SplitData.node4161 := by
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
  · rfl

def B4160 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617661576488929052983351655796310080] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4161, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq4160 : B4160.tree = HexagonCover.NBand.M8300_8500.SplitData.node4160 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4161
  · rfl
  · rfl
  · rfl

def B4159 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 42576834239985586553950069899605180448, 3367299772410400323541289854578316077287818334306368] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 618).pointIds 618), B4160]
theorem treeEq4159 : B4159.tree = HexagonCover.NBand.M8300_8500.SplitData.node4159 := by
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
  · exact treeEq4160

def B4165 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 43556184504254991601932977995236965220384, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 634).pointIds 634), (.leaf 6 (Common.fact 573).pointIds 573)]
theorem treeEq4165 : B4165.tree = HexagonCover.NBand.M8300_8500.SplitData.node4165 := by
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
  · rfl

def B4164 : Block := .branch 135 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3370222786835477263938873912319540701477239923408960] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4165, (.leaf 6 (Common.fact 576).pointIds 576)]
theorem treeEq4164 : B4164.tree = HexagonCover.NBand.M8300_8500.SplitData.node4164 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4165
  · rfl

def B4163 : Block := .branch 161 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 1496577676626845252854650389321924528368798608154632, 1393796574908163946345982392040522594222096, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B4164]
theorem treeEq4163 : B4163.tree = HexagonCover.NBand.M8300_8500.SplitData.node4163 := by
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
  · exact treeEq4164

def B4162 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560815458102466542654108135437928058323008] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4163, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 566).pointIds 566)]
theorem treeEq4162 : B4162.tree = HexagonCover.NBand.M8300_8500.SplitData.node4162 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4163
  · rfl
  · rfl
  · rfl

def B4158 : Block := .branch 125 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), B4159, B4162]
theorem treeEq4158 : B4158.tree = HexagonCover.NBand.M8300_8500.SplitData.node4158 := by
  change Tree.branch (125 : Fin 177) _ = Tree.branch (125 : Fin 177) _
  apply congrArg (Tree.branch (125 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4159
  · exact treeEq4162

def B4169 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626845252854571161159410264031205064204296, 98320, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 575).pointIds 575), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 636).pointIds 636)]
theorem treeEq4169 : B4169.tree = HexagonCover.NBand.M8300_8500.SplitData.node4169 := by
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
  · rfl

def B4168 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 393248, 3367299783604331724228473118501232970977385979052096] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4169, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 635).pointIds 635)]
theorem treeEq4168 : B4168.tree = HexagonCover.NBand.M8300_8500.SplitData.node4168 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4169
  · rfl
  · rfl
  · rfl

def B4167 : Block := .branch 135 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664613997892457936451903530140196872, 178405961588244985132285746181186892047941648, 748288838313422335658661502629357934307808096157728, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 634).pointIds 634), B4168]
theorem treeEq4167 : B4167.tree = HexagonCover.NBand.M8300_8500.SplitData.node4167 := by
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
  · exact treeEq4168

def B4166 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560775581262592995177921021226119647985728] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4167, (.leaf 6 (Common.fact 633).pointIds 633)]
theorem treeEq4166 : B4166.tree = HexagonCover.NBand.M8300_8500.SplitData.node4166 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4167
  · rfl

def B4157 : Block := .branch 121 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 664614077120620450716241123684147208, 179799758163153149078631728573227414642065424, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B4158, (.leaf 5 (Common.fact 256).pointIds 256), B4166]
theorem treeEq4157 : B4157.tree = HexagonCover.NBand.M8300_8500.SplitData.node4157 := by
  change Tree.branch (121 : Fin 177) _ = Tree.branch (121 : Fin 177) _
  apply congrArg (Tree.branch (121 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4158
  · rfl
  · exact treeEq4166

def B4174 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366802571251075863963217452757303033888, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 643).pointIds 643), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4174 : B4174.tree = HexagonCover.NBand.M8300_8500.SplitData.node4174 := by
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

def B4173 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944508450964441513226311388919841030176, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4174, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4173 : B4173.tree = HexagonCover.NBand.M8300_8500.SplitData.node4173 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4174
  · rfl

def B4172 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 233840261972944508450964441513226311388919841030176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 601).pointIds 601), (.leaf 5 (Common.fact 329).pointIds 329), B4173]
theorem treeEq4172 : B4172.tree = HexagonCover.NBand.M8300_8500.SplitData.node4172 := by
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
  · exact treeEq4173

def B4171 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 187072209578355615068446526866305254759929999654944, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 600).pointIds 600), B4172, (.leaf 0 [] 0)]
theorem treeEq4171 : B4171.tree = HexagonCover.NBand.M8300_8500.SplitData.node4171 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4172
  · rfl

def B4170 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393797240171198946120772297510364775546896, 41538374868278621028243970634154016, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 599).pointIds 599), B4171, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4170 : B4170.tree = HexagonCover.NBand.M8300_8500.SplitData.node4170 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4171
  · rfl

def B4156 : Block := .branch 119 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 41538374868278621028243970634154016, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 247).pointIds 247), (.leaf 1 (Common.fact 248).pointIds 248), (.leaf 2 (Common.fact 249).pointIds 249), B4157, B4170, (.leaf 5 (Common.fact 250).pointIds 250), (.leaf 6 (Common.fact 847).pointIds 847)]
theorem treeEq4156 : B4156.tree = HexagonCover.NBand.M8300_8500.SplitData.node4156 := by
  change Tree.branch (119 : Fin 177) _ = Tree.branch (119 : Fin 177) _
  apply congrArg (Tree.branch (119 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4157
  · exact treeEq4170
  · rfl
  · rfl

def B4136 : Block := .branch 115 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4136_4137, (.leaf 1 (Common.fact 243).pointIds 243), (.leaf 2 (Common.fact 244).pointIds 244), (.leaf 3 (Common.fact 245).pointIds 245), (.leaf 4 (Common.fact 246).pointIds 246), B4156, (.leaf 0 [] 0)]
theorem treeEq4136 : B4136.tree = HexagonCover.NBand.M8300_8500.SplitData.node4136 := by
  change Tree.branch (115 : Fin 177) _ = Tree.branch (115 : Fin 177) _
  apply congrArg (Tree.branch (115 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4156
  · rfl

theorem accepted4136 : B4136.accepted = true := by decide +kernel
theorem checked4136 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4136 (maskNeeds ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4136]
  exact B4136.sound accepted4136
#print axioms checked4136

def Tip4133_4136 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node4136 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] checked4136
def B4178 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 659).pointIds 659)]
theorem treeEq4178 : B4178.tree = HexagonCover.NBand.M8300_8500.SplitData.node4178 := by
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
  · rfl

def B4177 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822628046170205998708240412648454750272] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4178, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 657).pointIds 657)]
theorem treeEq4177 : B4177.tree = HexagonCover.NBand.M8300_8500.SplitData.node4177 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4178
  · rfl
  · rfl
  · rfl

def B4176 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400333925883571647971334348810992746560] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4177]
theorem treeEq4176 : B4176.tree = HexagonCover.NBand.M8300_8500.SplitData.node4176 := by
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
  · exact treeEq4177

def B4175 : Block := .branch 135 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772933191195142415830470672991745736768] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4176, (.leaf 6 (Common.fact 654).pointIds 654)]
theorem treeEq4175 : B4175.tree = HexagonCover.NBand.M8300_8500.SplitData.node4175 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4176
  · rfl

def B4135 : Block := .branch 113 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![Tip4133_4136, (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B4175]
theorem treeEq4135 : B4135.tree = HexagonCover.NBand.M8300_8500.SplitData.node4135 := by
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
  · exact treeEq4175

def B4183 : Block := .branch 125 ![2251799813685633, 1538, 6148, 24584, 98320, 982129100286366761032876207585342189208786669273120, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 257).pointIds 257), (.leaf 1 (Common.fact 258).pointIds 258), (.leaf 2 (Common.fact 259).pointIds 259), (.leaf 3 (Common.fact 260).pointIds 260), (.leaf 4 (Common.fact 261).pointIds 261), (.leaf 5 (Common.fact 560).pointIds 560), (.leaf 6 (Common.fact 585).pointIds 585)]
theorem treeEq4183 : B4183.tree = HexagonCover.NBand.M8300_8500.SplitData.node4183 := by
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

def B4182 : Block := .branch 169 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796574908163946345982392040522594222096, 233840261972944466912589573234605283144949207269408, 3378991796659420146152230904007905477769246547640384] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), B4183, (.leaf 6 (Common.fact 642).pointIds 642)]
theorem treeEq4182 : B4182.tree = HexagonCover.NBand.M8300_8500.SplitData.node4182 := by
  change Tree.branch (169 : Fin 177) _ = Tree.branch (169 : Fin 177) _
  apply congrArg (Tree.branch (169 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4183
  · rfl

def B4181 : Block := .branch 163 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 233840261972944466912589573234605283144949207269408, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), (.leaf 4 (Common.fact 646).pointIds 646), (.leaf 5 (Common.fact 329).pointIds 329), B4182]
theorem treeEq4181 : B4181.tree = HexagonCover.NBand.M8300_8500.SplitData.node4181 := by
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
  · exact treeEq4182

def B4180 : Block := .branch 165 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 187072209578355573530071658587684226515959365894176, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), (.leaf 4 (Common.fact 645).pointIds 645), B4181, (.leaf 0 [] 0)]
theorem treeEq4180 : B4180.tree = HexagonCover.NBand.M8300_8500.SplitData.node4180 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4181
  · rfl

def B4179 : Block := .branch 167 ![2251799813685633, 360358888689632770, 37778967891754180679684, 79228162514264337593543974920, 1393796575881719607321262572389990655950864, 393248, 3367299783560772922806601425346175213611999087296576] ![(.leaf 0 (Common.fact 500).pointIds 500), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 502).pointIds 502), (.leaf 3 (Common.fact 503).pointIds 503), (.leaf 4 (Common.fact 644).pointIds 644), B4180, (.leaf 6 (Common.fact 505).pointIds 505)]
theorem treeEq4179 : B4179.tree = HexagonCover.NBand.M8300_8500.SplitData.node4179 := by
  change Tree.branch (167 : Fin 177) _ = Tree.branch (167 : Fin 177) _
  apply congrArg (Tree.branch (167 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4180
  · rfl

def B4134 : Block := .branch 108 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B4135, B4179, (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 846).pointIds 846)]
theorem treeEq4134 : B4134.tree = HexagonCover.NBand.M8300_8500.SplitData.node4134 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4135
  · exact treeEq4179
  · rfl
  · rfl

def B4187 : Block := .branch 161 ![385, 1538, 4873482246350270879504388, 1496577676626844588240573268701473812127674924032008, 98320, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), (.leaf 2 (Common.fact 998).pointIds 998), (.leaf 3 (Common.fact 658).pointIds 658), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 757).pointIds 757)]
theorem treeEq4187 : B4187.tree = HexagonCover.NBand.M8300_8500.SplitData.node4187 := by
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
  · rfl

def B4186 : Block := .branch 170 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 24584, 178405961588244985132285746181186892047941648, 393248, 4115588610723822617662844139529281212753152499515456] ![(.leaf 0 (Common.fact 985).pointIds 985), (.leaf 1 (Common.fact 996).pointIds 996), (.leaf 2 (Common.fact 997).pointIds 997), B4187, (.leaf 4 (Common.fact 819).pointIds 819), (.leaf 5 (Common.fact 565).pointIds 565), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq4186 : B4186.tree = HexagonCover.NBand.M8300_8500.SplitData.node4186 := by
  change Tree.branch (170 : Fin 177) _ = Tree.branch (170 : Fin 177) _
  apply congrArg (Tree.branch (170 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq4187
  · rfl
  · rfl
  · rfl

def B4185 : Block := .branch 169 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 43556142965880123323311949751266331459616, 3367299772410400323542557505178544306689315037511744] ![(.leaf 0 (Common.fact 983).pointIds 983), (.leaf 1 (Common.fact 994).pointIds 994), (.leaf 2 (Common.fact 995).pointIds 995), (.leaf 3 (Common.fact 962).pointIds 962), (.leaf 4 (Common.fact 716).pointIds 716), (.leaf 5 (Common.fact 589).pointIds 589), B4186]
theorem treeEq4185 : B4185.tree = HexagonCover.NBand.M8300_8500.SplitData.node4185 := by
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
  · exact treeEq4186

def B4184 : Block := .branch 135 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163153149078631728573227414642065424, 393248, 3367299783560772922807869075946403443013495790501952] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), B4185, (.leaf 6 (Common.fact 751).pointIds 751)]
theorem treeEq4184 : B4184.tree = HexagonCover.NBand.M8300_8500.SplitData.node4184 := by
  change Tree.branch (135 : Fin 177) _ = Tree.branch (135 : Fin 177) _
  apply congrArg (Tree.branch (135 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4185
  · rfl

def B4133 : Block := .branch 100 ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064] ![B4134, (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), (.leaf 5 (Common.fact 206).pointIds 206), B4184]
theorem treeEq4133 : B4133.tree = HexagonCover.NBand.M8300_8500.SplitData.node4133 := by
  change Tree.branch (100 : Fin 177) _ = Tree.branch (100 : Fin 177) _
  apply congrArg (Tree.branch (100 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq4134
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq4184

theorem accepted4133 : B4133.accepted = true := by decide +kernel
theorem checked4133 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node4133 (maskNeeds ![2251799813685633, 360358888689632770, 4873482246350270879504388, 79228162514264337593543974920, 179799758163802186185948582026793726683217936, 393248, 3367299783582556311201524626671322803715873374208064]) := by
  rw [← treeEq4133]
  exact B4133.sound accepted4133
#print axioms checked4133

end HexagonCover.NBand.M8300_8500.SplitTree.Run0057
