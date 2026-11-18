import HexagonCover.NBand.M6667_6700.SplitData
import HexagonCover.NBand.M6667_6700.SplitTree.Run0031
import HexagonCover.NBand.M6667_6700.SplitTree.Run0033
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M6667_6700.SplitTree.Run0034
open OwnerTree HexagonCover.NBand.M6667_6700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1334) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def Tip2288_2305 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2305 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664098140005042819234551690989808356163648] HexagonCover.NBand.M6667_6700.SplitTree.Run0031.checked2305
def Tip2288_2337 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2337 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089502943103374907104242591572367507520] HexagonCover.NBand.M6667_6700.SplitTree.Run0031.checked2337
def Tip2288_2356 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2356 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] HexagonCover.NBand.M6667_6700.SplitTree.Run0033.checked2356
def B2292 : Block := .branch 132 ![385, 1538, 6148, 24584, 664613997892457936451903530140270608, 393248, 7108743963977511794467875405290541449090910016503872] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 421).pointIds 421), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 664).pointIds 664)]
theorem treeEq2292 : B2292.tree = HexagonCover.NBand.M6667_6700.SplitData.node2292 := by
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

def B2291 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 664613997892457936451903530140270608, 393248, 6360455125664089500347588770939804543027072554500160] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 371).pointIds 371), B2292]
theorem treeEq2291 : B2291.tree = HexagonCover.NBand.M6667_6700.SplitData.node2291 := by
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
  · exact treeEq2292

def B2295 : Block := .branch 132 ![385, 1538, 6148, 24584, 1329227995784915872903807060280442896, 393248, 7108743963977512458757354744090051174211284136099904] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 665).pointIds 665)]
theorem treeEq2295 : B2295.tree = HexagonCover.NBand.M6667_6700.SplitData.node2295 := by
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

def B2294 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 1329227995784915872903807060280442896, 393248, 6360455125664090164637068109739314268147446674096192] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 423).pointIds 423), (.leaf 5 (Common.fact 371).pointIds 371), B2295]
theorem treeEq2294 : B2294.tree = HexagonCover.NBand.M6667_6700.SplitData.node2294 := by
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
  · exact treeEq2295

def B2298 : Block := .branch 132 ![385, 1538, 6148, 24584, 2658455991569831745807614120560787472, 393248, 9353610478917780007030286754233905251438950744588352] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 669).pointIds 669), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 670).pointIds 670)]
theorem treeEq2298 : B2298.tree = HexagonCover.NBand.M6667_6700.SplitData.node2298 := by
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

def B2297 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 2658455991569831745807614120560787472, 393248, 6360455125664090830549140216830957627183600896573504] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 668).pointIds 668), (.leaf 5 (Common.fact 909).pointIds 909), B2298]
theorem treeEq2297 : B2297.tree = HexagonCover.NBand.M6667_6700.SplitData.node2297 := by
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
  · exact treeEq2298

def B2304 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 674).pointIds 674)]
theorem treeEq2304 : B2304.tree = HexagonCover.NBand.M6667_6700.SplitData.node2304 := by
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

def B2303 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372512514172072772167606254140855295972980326662208] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2304, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 673).pointIds 673)]
theorem treeEq2303 : B2303.tree = HexagonCover.NBand.M6667_6700.SplitData.node2303 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2304
  · rfl
  · rfl

def B2302 : Block := .branch 158 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6372147138762740046438055332932676225218066343526464] ![(.leaf 0 (Common.fact 1181).pointIds 1181), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2303]
theorem treeEq2302 : B2302.tree = HexagonCover.NBand.M6667_6700.SplitData.node2302 := by
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
  · exact treeEq2303

def B2301 : Block := .branch 140 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6372147138762740046438689158232790339918814695129152] ![(.leaf 0 (Common.fact 194).pointIds 194), (.leaf 1 (Common.fact 195).pointIds 195), (.leaf 2 (Common.fact 196).pointIds 196), (.leaf 3 (Common.fact 197).pointIds 197), B2302, (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 671).pointIds 671)]
theorem treeEq2301 : B2301.tree = HexagonCover.NBand.M6667_6700.SplitData.node2301 := by
  change Tree.branch (140 : Fin 173) _ = Tree.branch (140 : Fin 173) _
  apply congrArg (Tree.branch (140 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2302
  · rfl
  · rfl

def B2300 : Block := .branch 163 ![5316911983139664081911038599827030401, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![(.leaf 0 (Common.fact 1180).pointIds 1180), (.leaf 1 (Common.fact 527).pointIds 527), (.leaf 2 (Common.fact 528).pointIds 528), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 531).pointIds 531), B2301]
theorem treeEq2300 : B2300.tree = HexagonCover.NBand.M6667_6700.SplitData.node2300 := by
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
  · exact treeEq2301

def B2299 : Block := .branch 122 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664092823093059679571060075761567234785344] ![B2300, (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), Tip2288_2305]
theorem treeEq2299 : B2299.tree = HexagonCover.NBand.M6667_6700.SplitData.node2299 := by
  change Tree.branch (122 : Fin 173) _ = Tree.branch (122 : Fin 173) _
  apply congrArg (Tree.branch (122 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2300
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2296 : Block := .branch 121 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664091495163138109288894079087131036745792] ![(.leaf 0 (Common.fact 426).pointIds 426), (.leaf 1 (Common.fact 427).pointIds 427), (.leaf 2 (Common.fact 428).pointIds 428), (.leaf 3 (Common.fact 429).pointIds 429), B2297, (.leaf 5 (Common.fact 430).pointIds 430), B2299]
theorem treeEq2296 : B2296.tree = HexagonCover.NBand.M6667_6700.SplitData.node2296 := by
  change Tree.branch (121 : Fin 173) _ = Tree.branch (121 : Fin 173) _
  apply congrArg (Tree.branch (121 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2297
  · rfl
  · exact treeEq2299

def B2293 : Block := .branch 120 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664090165935142324373021175280070756401216] ![(.leaf 0 (Common.fact 159).pointIds 159), (.leaf 1 (Common.fact 160).pointIds 160), (.leaf 2 (Common.fact 161).pointIds 161), (.leaf 3 (Common.fact 162).pointIds 162), B2294, (.leaf 5 (Common.fact 163).pointIds 163), B2296]
theorem treeEq2293 : B2293.tree = HexagonCover.NBand.M6667_6700.SplitData.node2293 := by
  change Tree.branch (120 : Fin 173) _ = Tree.branch (120 : Fin 173) _
  apply congrArg (Tree.branch (120 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2294
  · rfl
  · exact treeEq2296

def B2290 : Block := .branch 119 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664089501645662985573511450159696636805184] ![(.leaf 0 (Common.fact 415).pointIds 415), (.leaf 1 (Common.fact 416).pointIds 416), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 418).pointIds 418), B2291, (.leaf 5 (Common.fact 419).pointIds 419), B2293]
theorem treeEq2290 : B2290.tree = HexagonCover.NBand.M6667_6700.SplitData.node2290 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2291
  · rfl
  · exact treeEq2293

def B2289 : Block := .branch 111 ![590295810358705652097, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![B2290, (.leaf 1 (Common.fact 154).pointIds 154), (.leaf 2 (Common.fact 155).pointIds 155), (.leaf 3 (Common.fact 156).pointIds 156), (.leaf 4 (Common.fact 157).pointIds 157), (.leaf 5 (Common.fact 158).pointIds 158), Tip2288_2337]
theorem treeEq2289 : B2289.tree = HexagonCover.NBand.M6667_6700.SplitData.node2289 := by
  change Tree.branch (111 : Fin 173) _ = Tree.branch (111 : Fin 173) _
  apply congrArg (Tree.branch (111 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2290
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2288 : Block := .branch 69 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] ![B2289, Tip2288_2356, (.leaf 2 (Common.fact 149).pointIds 149), (.leaf 3 (Common.fact 150).pointIds 150), (.leaf 4 (Common.fact 151).pointIds 151), (.leaf 5 (Common.fact 152).pointIds 152), (.leaf 6 (Common.fact 1011).pointIds 1011)]
theorem treeEq2288 : B2288.tree = HexagonCover.NBand.M6667_6700.SplitData.node2288 := by
  change Tree.branch (69 : Fin 173) _ = Tree.branch (69 : Fin 173) _
  apply congrArg (Tree.branch (69 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2289
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted2288 : B2288.accepted = true := by decide +kernel
theorem checked2288 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2288 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184]) := by
  rw [← treeEq2288]
  exact B2288.sound accepted2288
#print axioms checked2288

def Tip2281_2288 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2288 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501645662985573511450159696636805184] checked2288
def B2287 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1010).pointIds 1010)]
theorem treeEq2287 : B2287.tree = HexagonCover.NBand.M6667_6700.SplitData.node2287 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2286 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 7108743963977511794143673764282171779658128171728960] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2287, (.leaf 6 (Common.fact 1006).pointIds 1006)]
theorem treeEq2286 : B2286.tree = HexagonCover.NBand.M6667_6700.SplitData.node2286 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2287
  · rfl

def B2285 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 324518553658426726783156020674576, 393248, 6360455125664089500023387129931434873594290709725248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 376).pointIds 376), (.leaf 5 (Common.fact 371).pointIds 371), B2286]
theorem treeEq2285 : B2285.tree = HexagonCover.NBand.M6667_6700.SplitData.node2285 := by
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
  · exact treeEq2286

def B2284 : Block := .branch 108 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 132).pointIds 132), (.leaf 1 (Common.fact 133).pointIds 133), (.leaf 2 (Common.fact 134).pointIds 134), (.leaf 3 (Common.fact 135).pointIds 135), B2285, (.leaf 5 (Common.fact 136).pointIds 136), Tip2281_2288]
theorem treeEq2284 : B2284.tree = HexagonCover.NBand.M6667_6700.SplitData.node2284 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2285
  · rfl
  · rfl

def B2503 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1033).pointIds 1033)]
theorem treeEq2503 : B2503.tree = HexagonCover.NBand.M6667_6700.SplitData.node2503 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2502 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794145575240182514123760373226537024] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2503, (.leaf 6 (Common.fact 1030).pointIds 1030)]
theorem treeEq2502 : B2502.tree = HexagonCover.NBand.M6667_6700.SplitData.node2502 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2503
  · rfl

def B2501 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500025288605831777217696535764533312] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2502]
theorem treeEq2501 : B2501.tree = HexagonCover.NBand.M6667_6700.SplitData.node2501 := by
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
  · exact treeEq2502

def B2500 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501323362820465484124829159846838336] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2501, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1029).pointIds 1029)]
theorem treeEq2500 : B2500.tree = HexagonCover.NBand.M6667_6700.SplitData.node2500 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2501
  · rfl
  · rfl

def B2283 : Block := .branch 101 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![B2284, (.leaf 1 (Common.fact 127).pointIds 127), (.leaf 2 (Common.fact 128).pointIds 128), (.leaf 3 (Common.fact 129).pointIds 129), (.leaf 4 (Common.fact 130).pointIds 130), (.leaf 5 (Common.fact 131).pointIds 131), B2500]
theorem treeEq2283 : B2283.tree = HexagonCover.NBand.M6667_6700.SplitData.node2283 := by
  change Tree.branch (101 : Fin 173) _ = Tree.branch (101 : Fin 173) _
  apply congrArg (Tree.branch (101 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2284
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2500

def B2507 : Block := .branch 133 ![385, 1538, 6148, 24584, 98320, 187072209578355573530071658587684226515959365894176, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 174).pointIds 174), (.leaf 1 (Common.fact 175).pointIds 175), (.leaf 2 (Common.fact 176).pointIds 176), (.leaf 3 (Common.fact 177).pointIds 177), (.leaf 4 (Common.fact 178).pointIds 178), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 1036).pointIds 1036)]
theorem treeEq2507 : B2507.tree = HexagonCover.NBand.M6667_6700.SplitData.node2507 := by
  change Tree.branch (133 : Fin 173) _ = Tree.branch (133 : Fin 173) _
  apply congrArg (Tree.branch (133 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2506 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511795441116629495843142850553700679744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), B2507, (.leaf 6 (Common.fact 1035).pointIds 1035)]
theorem treeEq2506 : B2506.tree = HexagonCover.NBand.M6667_6700.SplitData.node2506 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2507
  · rfl

def B2505 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2506]
theorem treeEq2505 : B2505.tree = HexagonCover.NBand.M6667_6700.SplitData.node2505 := by
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
  · exact treeEq2506

def B2504 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320829995145106236786716238676032] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2505, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1034).pointIds 1034)]
theorem treeEq2504 : B2504.tree = HexagonCover.NBand.M6667_6700.SplitData.node2504 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2505
  · rfl
  · rfl

def B2282 : Block := .branch 91 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![B2283, (.leaf 1 (Common.fact 122).pointIds 122), (.leaf 2 (Common.fact 123).pointIds 123), (.leaf 3 (Common.fact 124).pointIds 124), (.leaf 4 (Common.fact 125).pointIds 125), (.leaf 5 (Common.fact 126).pointIds 126), B2504]
theorem treeEq2282 : B2282.tree = HexagonCover.NBand.M6667_6700.SplitData.node2282 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2283
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2504

def B2511 : Block := .branch 141 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 179).pointIds 179), (.leaf 1 (Common.fact 180).pointIds 180), (.leaf 2 (Common.fact 181).pointIds 181), (.leaf 3 (Common.fact 182).pointIds 182), (.leaf 4 (Common.fact 1031).pointIds 1031), (.leaf 5 (Common.fact 1032).pointIds 1032), (.leaf 6 (Common.fact 1039).pointIds 1039)]
theorem treeEq2511 : B2511.tree = HexagonCover.NBand.M6667_6700.SplitData.node2511 := by
  change Tree.branch (141 : Fin 173) _ = Tree.branch (141 : Fin 173) _
  apply congrArg (Tree.branch (141 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2510 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143040557952077307647517269688384] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2511, (.leaf 6 (Common.fact 1038).pointIds 1038)]
theorem treeEq2510 : B2510.tree = HexagonCover.NBand.M6667_6700.SplitData.node2510 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2511
  · rfl

def B2509 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500022753923601340401583679807684672] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2510]
theorem treeEq2509 : B2509.tree = HexagonCover.NBand.M6667_6700.SplitData.node2509 := by
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
  · exact treeEq2510

def B2508 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501320828138235047308716303889989696] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2509, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1037).pointIds 1037)]
theorem treeEq2508 : B2508.tree = HexagonCover.NBand.M6667_6700.SplitData.node2508 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2509
  · rfl
  · rfl

def B2281 : Block := .branch 89 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 117).pointIds 117), B2282, (.leaf 2 (Common.fact 118).pointIds 118), (.leaf 3 (Common.fact 119).pointIds 119), (.leaf 4 (Common.fact 120).pointIds 120), (.leaf 5 (Common.fact 121).pointIds 121), B2508]
theorem treeEq2281 : B2281.tree = HexagonCover.NBand.M6667_6700.SplitData.node2281 := by
  change Tree.branch (89 : Fin 173) _ = Tree.branch (89 : Fin 173) _
  apply congrArg (Tree.branch (89 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq2282
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2508

theorem accepted2281 : B2281.accepted = true := by decide +kernel
theorem checked2281 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2281 (maskNeeds ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272]) := by
  rw [← treeEq2281]
  exact B2281.sound accepted2281
#print axioms checked2281

def Tip2276_2281 : Block := .tip HexagonCover.NBand.M6667_6700.SplitData.node2281 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] checked2281
def B2515 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 1496577676626844588240573268701473812127674924400672, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), (.leaf 4 (Common.fact 737).pointIds 737), (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 756).pointIds 756)]
theorem treeEq2515 : B2515.tree = HexagonCover.NBand.M6667_6700.SplitData.node2515 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B2514 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356929003367177644021177122880] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2515, (.leaf 6 (Common.fact 754).pointIds 754)]
theorem treeEq2514 : B2514.tree = HexagonCover.NBand.M6667_6700.SplitData.node2514 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2515
  · rfl

def B2513 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070294652630271580183715119168] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2514]
theorem treeEq2513 : B2513.tree = HexagonCover.NBand.M6667_6700.SplitData.node2513 := by
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
  · exact treeEq2514

def B2512 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461421936394236063181973225536] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2513, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 750).pointIds 750)]
theorem treeEq2512 : B2512.tree = HexagonCover.NBand.M6667_6700.SplitData.node2512 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2513
  · rfl
  · rfl

def B2280 : Block := .branch 86 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 112).pointIds 112), (.leaf 1 (Common.fact 113).pointIds 113), (.leaf 2 (Common.fact 114).pointIds 114), Tip2276_2281, (.leaf 4 (Common.fact 115).pointIds 115), (.leaf 5 (Common.fact 116).pointIds 116), B2512]
theorem treeEq2280 : B2280.tree = HexagonCover.NBand.M6667_6700.SplitData.node2280 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2512

def B2518 : Block := .branch 132 ![385, 1538, 6148, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 7108743963977511794143356890317740949975887586525248] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 870).pointIds 870), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1041).pointIds 1041)]
theorem treeEq2518 : B2518.tree = HexagonCover.NBand.M6667_6700.SplitData.node2518 := by
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

def B2517 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 24584, 2993155710065612352971116801974439986629133943799824, 393248, 6360455125664089500023070255967004043912050124521536] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), (.leaf 4 (Common.fact 730).pointIds 730), (.leaf 5 (Common.fact 371).pointIds 371), B2518]
theorem treeEq2517 : B2517.tree = HexagonCover.NBand.M6667_6700.SplitData.node2517 := by
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
  · exact treeEq2518

def B2516 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321144470600710951044674206826560] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2517, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 1040).pointIds 1040)]
theorem treeEq2516 : B2516.tree = HexagonCover.NBand.M6667_6700.SplitData.node2516 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2517
  · rfl
  · rfl

def B2279 : Block := .branch 85 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461344565141780726914792030272] ![(.leaf 0 (Common.fact 107).pointIds 107), (.leaf 1 (Common.fact 108).pointIds 108), (.leaf 2 (Common.fact 109).pointIds 109), B2280, (.leaf 4 (Common.fact 110).pointIds 110), (.leaf 5 (Common.fact 111).pointIds 111), B2516]
theorem treeEq2279 : B2279.tree = HexagonCover.NBand.M6667_6700.SplitData.node2279 := by
  change Tree.branch (85 : Fin 173) _ = Tree.branch (85 : Fin 173) _
  apply congrArg (Tree.branch (85 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2280
  · rfl
  · rfl
  · exact treeEq2516

def B2278 : Block := .branch 137 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 402).pointIds 402), (.leaf 1 (Common.fact 403).pointIds 403), (.leaf 2 (Common.fact 404).pointIds 404), (.leaf 3 (Common.fact 997).pointIds 997), B2279, (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 998).pointIds 998)]
theorem treeEq2278 : B2278.tree = HexagonCover.NBand.M6667_6700.SplitData.node2278 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2279
  · rfl
  · rfl

def B2277 : Block := .branch 138 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 643).pointIds 643), (.leaf 1 (Common.fact 644).pointIds 644), (.leaf 2 (Common.fact 645).pointIds 645), (.leaf 3 (Common.fact 995).pointIds 995), B2278, (.leaf 5 (Common.fact 647).pointIds 647), (.leaf 6 (Common.fact 996).pointIds 996)]
theorem treeEq2277 : B2277.tree = HexagonCover.NBand.M6667_6700.SplitData.node2277 := by
  change Tree.branch (138 : Fin 173) _ = Tree.branch (138 : Fin 173) _
  apply congrArg (Tree.branch (138 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2278
  · rfl
  · rfl

def B2521 : Block := .branch 132 ![385, 1538, 6148, 24584, 187072209578355573530071658587684226515959365599248, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 137).pointIds 137), (.leaf 1 (Common.fact 138).pointIds 138), (.leaf 2 (Common.fact 139).pointIds 139), (.leaf 3 (Common.fact 140).pointIds 140), (.leaf 4 (Common.fact 802).pointIds 802), (.leaf 5 (Common.fact 142).pointIds 142), (.leaf 6 (Common.fact 1044).pointIds 1044)]
theorem treeEq2521 : B2521.tree = HexagonCover.NBand.M6667_6700.SplitData.node2521 := by
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

def B2520 : Block := .branch 167 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 1496577676626844588240573268701473812127674924400672, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1173).pointIds 1173), (.leaf 1 (Common.fact 1174).pointIds 1174), (.leaf 2 (Common.fact 1175).pointIds 1175), (.leaf 3 (Common.fact 1176).pointIds 1176), B2521, (.leaf 5 (Common.fact 738).pointIds 738), (.leaf 6 (Common.fact 1043).pointIds 1043)]
theorem treeEq2520 : B2520.tree = HexagonCover.NBand.M6667_6700.SplitData.node2520 := by
  change Tree.branch (167 : Fin 173) _ = Tree.branch (167 : Fin 173) _
  apply congrArg (Tree.branch (167 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2521
  · rfl
  · rfl

def B2519 : Block := .branch 170 ![385, 1297037792194332162, 9007199254747140, 24584, 98320, 393248, 6360455125664089501321144451257897837210607411527744] ![(.leaf 0 (Common.fact 1169).pointIds 1169), (.leaf 1 (Common.fact 1170).pointIds 1170), (.leaf 2 (Common.fact 1171).pointIds 1171), (.leaf 3 (Common.fact 1172).pointIds 1172), (.leaf 4 (Common.fact 1005).pointIds 1005), B2520, (.leaf 6 (Common.fact 1042).pointIds 1042)]
theorem treeEq2519 : B2519.tree = HexagonCover.NBand.M6667_6700.SplitData.node2519 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2520
  · rfl

def B2276 : Block := .branch 84 ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328] ![(.leaf 0 (Common.fact 102).pointIds 102), (.leaf 1 (Common.fact 103).pointIds 103), (.leaf 2 (Common.fact 104).pointIds 104), B2277, (.leaf 4 (Common.fact 105).pointIds 105), (.leaf 5 (Common.fact 106).pointIds 106), B2519]
theorem treeEq2276 : B2276.tree = HexagonCover.NBand.M6667_6700.SplitData.node2276 := by
  change Tree.branch (84 : Fin 173) _ = Tree.branch (84 : Fin 173) _
  apply congrArg (Tree.branch (84 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq2277
  · rfl
  · rfl
  · exact treeEq2519

theorem accepted2276 : B2276.accepted = true := by decide +kernel
theorem checked2276 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2276 (maskNeeds ![385, 1297037792194332162, 18455751272964298756, 2361183241434822631432, 356811923176489970264571492362373784095784976, 393248, 6360455125664089501321461654050151602071983516811328]) := by
  rw [← treeEq2276]
  exact B2276.sound accepted2276
#print axioms checked2276

def B2575 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2575 : B2575.tree = HexagonCover.NBand.M6667_6700.SplitData.node2575 := by
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

def B2574 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2575, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2574 : B2574.tree = HexagonCover.NBand.M6667_6700.SplitData.node2574 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2575
  · rfl
  · rfl

def B2573 : Block := .branch 158 ![10636420114708594987340532089113018753, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1183).pointIds 1183), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2574]
theorem treeEq2573 : B2573.tree = HexagonCover.NBand.M6667_6700.SplitData.node2573 := by
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
  · exact treeEq2574

def B2578 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2578 : B2578.tree = HexagonCover.NBand.M6667_6700.SplitData.node2578 := by
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

def B2577 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2578]
theorem treeEq2577 : B2577.tree = HexagonCover.NBand.M6667_6700.SplitData.node2577 := by
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
  · exact treeEq2578

def B2576 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2577, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2576 : B2576.tree = HexagonCover.NBand.M6667_6700.SplitData.node2576 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2577
  · rfl
  · rfl

def B2572 : Block := .branch 123 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2573, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2576]
theorem treeEq2572 : B2572.tree = HexagonCover.NBand.M6667_6700.SplitData.node2572 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2573
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2576

def B2582 : Block := .branch 131 ![385, 1538, 6148, 24584, 2993155354647485751389310483748930016295872442236944, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 143).pointIds 143), (.leaf 1 (Common.fact 144).pointIds 144), (.leaf 2 (Common.fact 145).pointIds 145), (.leaf 3 (Common.fact 146).pointIds 146), (.leaf 4 (Common.fact 635).pointIds 635), (.leaf 5 (Common.fact 148).pointIds 148), (.leaf 6 (Common.fact 955).pointIds 955)]
theorem treeEq2582 : B2582.tree = HexagonCover.NBand.M6667_6700.SplitData.node2582 := by
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

def B2581 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360820501073430865733959915218174510769888311115840] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), B2582, (.leaf 5 (Common.fact 909).pointIds 909), (.leaf 6 (Common.fact 954).pointIds 954)]
theorem treeEq2581 : B2581.tree = HexagonCover.NBand.M6667_6700.SplitData.node2581 := by
  change Tree.branch (171 : Fin 173) _ = Tree.branch (171 : Fin 173) _
  apply congrArg (Tree.branch (171 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2582
  · rfl
  · rfl

def B2580 : Block := .branch 158 ![10636420114708594987340532089113018753, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![(.leaf 0 (Common.fact 1183).pointIds 1183), (.leaf 1 (Common.fact 1182).pointIds 1182), (.leaf 2 (Common.fact 219).pointIds 219), (.leaf 3 (Common.fact 220).pointIds 220), (.leaf 4 (Common.fact 221).pointIds 221), (.leaf 5 (Common.fact 222).pointIds 222), B2581]
theorem treeEq2580 : B2580.tree = HexagonCover.NBand.M6667_6700.SplitData.node2580 := by
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
  · exact treeEq2581

def B2585 : Block := .branch 128 ![385, 1538, 6148, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 9353610478917789310327549208786752419980914596511808] ![(.leaf 0 (Common.fact 434).pointIds 434), (.leaf 1 (Common.fact 435).pointIds 435), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 1018).pointIds 1018), (.leaf 4 (Common.fact 622).pointIds 622), (.leaf 5 (Common.fact 439).pointIds 439), (.leaf 6 (Common.fact 937).pointIds 937)]
theorem treeEq2585 : B2585.tree = HexagonCover.NBand.M6667_6700.SplitData.node2585 := by
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

def B2584 : Block := .branch 171 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 748288838313422294120286634350736906063837462102032, 393248, 6360455125664100133846402671383804795725564748496960] ![(.leaf 0 (Common.fact 1177).pointIds 1177), (.leaf 1 (Common.fact 1178).pointIds 1178), (.leaf 2 (Common.fact 1179).pointIds 1179), (.leaf 3 (Common.fact 1014).pointIds 1014), (.leaf 4 (Common.fact 540).pointIds 540), (.leaf 5 (Common.fact 909).pointIds 909), B2585]
theorem treeEq2584 : B2584.tree = HexagonCover.NBand.M6667_6700.SplitData.node2584 := by
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
  · exact treeEq2585

def B2583 : Block := .branch 169 ![385, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 98320, 393248, 6360455125664100798460400563841741247629094888669248] ![(.leaf 0 (Common.fact 1163).pointIds 1163), (.leaf 1 (Common.fact 1164).pointIds 1164), (.leaf 2 (Common.fact 1165).pointIds 1165), (.leaf 3 (Common.fact 1166).pointIds 1166), B2584, (.leaf 5 (Common.fact 371).pointIds 371), (.leaf 6 (Common.fact 936).pointIds 936)]
theorem treeEq2583 : B2583.tree = HexagonCover.NBand.M6667_6700.SplitData.node2583 := by
  change Tree.branch (169 : Fin 173) _ = Tree.branch (169 : Fin 173) _
  apply congrArg (Tree.branch (169 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2584
  · rfl
  · rfl

def B2579 : Block := .branch 123 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140004408994009995440014974327980096] ![B2580, (.leaf 1 (Common.fact 164).pointIds 164), (.leaf 2 (Common.fact 165).pointIds 165), (.leaf 3 (Common.fact 166).pointIds 166), (.leaf 4 (Common.fact 167).pointIds 167), (.leaf 5 (Common.fact 168).pointIds 168), B2583]
theorem treeEq2579 : B2579.tree = HexagonCover.NBand.M6667_6700.SplitData.node2579 := by
  change Tree.branch (123 : Fin 173) _ = Tree.branch (123 : Fin 173) _
  apply congrArg (Tree.branch (123 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq2580
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq2583

def B2571 : Block := .branch 74 ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784] ![(.leaf 0 (Common.fact 921).pointIds 921), (.leaf 1 (Common.fact 922).pointIds 922), B2572, B2579, (.leaf 4 (Common.fact 923).pointIds 923), (.leaf 5 (Common.fact 924).pointIds 924), (.leaf 6 (Common.fact 940).pointIds 940)]
theorem treeEq2571 : B2571.tree = HexagonCover.NBand.M6667_6700.SplitData.node2571 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq2572
  · exact treeEq2579
  · rfl
  · rfl
  · rfl

theorem accepted2571 : B2571.accepted = true := by decide +kernel
theorem checked2571 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M6667_6700.SplitData.node2571 (maskNeeds ![2596148429268004110075606870262145, 1297037792194332162, 9007199254747140, 19345174297075501617930248, 1393796574908163946345982392040522594222096, 393248, 6360455125664098140005042819310109554715722679582784]) := by
  rw [← treeEq2571]
  exact B2571.sound accepted2571
#print axioms checked2571

end HexagonCover.NBand.M6667_6700.SplitTree.Run0034
