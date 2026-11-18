import HexagonCover.NBand.M8300_8500.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8300_8500.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M8300_8500

abbrev Block := Chunk (n := 177) (Certificate := Fin 1786) (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck

def B0073 : Block := .branch 171 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M8300_8500.SplitData.node0073 := by
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

def B0072 : Block := .branch 170 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 372).pointIds 372), (.leaf 2 (Common.fact 373).pointIds 373), (.leaf 3 (Common.fact 374).pointIds 374), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), B0073]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M8300_8500.SplitData.node0072 := by
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
  · exact treeEq0073

def B0071 : Block := .branch 169 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 366).pointIds 366), (.leaf 2 (Common.fact 367).pointIds 367), (.leaf 3 (Common.fact 368).pointIds 368), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0072]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M8300_8500.SplitData.node0071 := by
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
  · exact treeEq0072

def B0070 : Block := .branch 168 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0071]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M8300_8500.SplitData.node0070 := by
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
  · exact treeEq0071

def B0077 : Block := .branch 171 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 52614058943912505055332653977786188707613571645456, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 390).pointIds 390), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M8300_8500.SplitData.node0077 := by
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

def B0076 : Block := .branch 170 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 52614058943912505055332653977786188707613571645456, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 372).pointIds 372), (.leaf 2 (Common.fact 373).pointIds 373), (.leaf 3 (Common.fact 388).pointIds 388), (.leaf 4 (Common.fact 389).pointIds 389), (.leaf 5 (Common.fact 376).pointIds 376), B0077]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M8300_8500.SplitData.node0076 := by
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
  · exact treeEq0077

def B0075 : Block := .branch 169 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 52614058943912505055332653977786188707613571645456, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 366).pointIds 366), (.leaf 2 (Common.fact 367).pointIds 367), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 387).pointIds 387), (.leaf 5 (Common.fact 370).pointIds 370), B0076]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M8300_8500.SplitData.node0075 := by
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
  · exact treeEq0076

def B0074 : Block := .branch 168 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 52614058943912505055332653977786188707613571645456, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 364).pointIds 364), B0075]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M8300_8500.SplitData.node0074 := by
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
  · exact treeEq0075

def B0079 : Block := .branch 169 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 379990436856407357998269627274092721435272969453632] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 366).pointIds 366), (.leaf 2 (Common.fact 367).pointIds 367), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 392).pointIds 392)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M8300_8500.SplitData.node0079 := by
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

def B0078 : Block := .branch 168 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 5846017699696210938126310098724268403354238451776] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0079]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M8300_8500.SplitData.node0078 := by
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
  · exact treeEq0079

def B0069 : Block := .branch 162 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), B0070, B0074, (.leaf 5 (Common.fact 358).pointIds 358), B0078]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M8300_8500.SplitData.node0069 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0070
  · exact treeEq0074
  · rfl
  · exact treeEq0078

def B0083 : Block := .branch 171 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 2923092477642599958899935808305656632757889032200, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 399).pointIds 399), (.leaf 3 (Common.fact 400).pointIds 400), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M8300_8500.SplitData.node0083 := by
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

def B0082 : Block := .branch 170 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 2923092477642599958899935808305656632757889032200, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 372).pointIds 372), (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 398).pointIds 398), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), B0083]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M8300_8500.SplitData.node0082 := by
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
  · exact treeEq0083

def B0081 : Block := .branch 169 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 2923092477642599958899935808305656632757889032200, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 366).pointIds 366), (.leaf 2 (Common.fact 395).pointIds 395), (.leaf 3 (Common.fact 396).pointIds 396), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0082]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M8300_8500.SplitData.node0081 := by
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
  · exact treeEq0082

def B0080 : Block := .branch 168 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 2923092477642599958899935808305656632757889032200, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 393).pointIds 393), (.leaf 3 (Common.fact 394).pointIds 394), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0081]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M8300_8500.SplitData.node0080 := by
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
  · exact treeEq0081

def B0085 : Block := .branch 169 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 377067433581745552161862257608660155395961104367680] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 366).pointIds 366), (.leaf 2 (Common.fact 395).pointIds 395), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M8300_8500.SplitData.node0085 := by
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

def B0084 : Block := .branch 168 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2923014425034405101718940433291702364042373365824] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 393).pointIds 393), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0085]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M8300_8500.SplitData.node0084 := by
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
  · exact treeEq0085

def B0068 : Block := .branch 161 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0069, B0080, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), B0084]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M8300_8500.SplitData.node0068 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0069
  · exact treeEq0080
  · rfl
  · rfl
  · exact treeEq0084

theorem accepted0068 : B0068.accepted = true := by decide +kernel
theorem checked0068 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0068 (maskNeeds ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872]) := by
  rw [← treeEq0068]
  exact B0068.sound accepted0068
#print axioms checked0068

def Tip0066_0068 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0068 ![57115899269183218607248760090132865, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872] checked0068
def B0089 : Block := .branch 171 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 390).pointIds 390), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M8300_8500.SplitData.node0089 := by
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

def B0088 : Block := .branch 170 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 406).pointIds 406), (.leaf 2 (Common.fact 407).pointIds 407), (.leaf 3 (Common.fact 388).pointIds 388), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), B0089]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M8300_8500.SplitData.node0088 := by
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
  · exact treeEq0089

def B0087 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 405).pointIds 405), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0088]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M8300_8500.SplitData.node0087 := by
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
  · exact treeEq0088

def B0086 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 403).pointIds 403), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0087]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M8300_8500.SplitData.node0086 := by
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
  · exact treeEq0087

def B0091 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 375605931944414649243658572775943872376305171824704] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 395).pointIds 395), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M8300_8500.SplitData.node0091 := by
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

def B0090 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1461512787703502183515255600575419344386440822848] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 393).pointIds 393), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0091]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M8300_8500.SplitData.node0090 := by
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
  · exact treeEq0091

def B0067 : Block := .branch 160 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 347).pointIds 347), Tip0066_0068, B0086, (.leaf 3 (Common.fact 348).pointIds 348), (.leaf 4 (Common.fact 349).pointIds 349), (.leaf 5 (Common.fact 350).pointIds 350), B0090]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M8300_8500.SplitData.node0067 := by
  change Tree.branch (160 : Fin 177) _ = Tree.branch (160 : Fin 177) _
  apply congrArg (Tree.branch (160 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0086
  · rfl
  · rfl
  · rfl
  · exact treeEq0090

def B0097 : Block := .branch 171 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M8300_8500.SplitData.node0097 := by
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

def B0096 : Block := .branch 170 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 406).pointIds 406), (.leaf 2 (Common.fact 419).pointIds 419), (.leaf 3 (Common.fact 420).pointIds 420), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), B0097]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M8300_8500.SplitData.node0096 := by
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
  · exact treeEq0097

def B0095 : Block := .branch 161 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0096, (.leaf 3 (Common.fact 417).pointIds 417), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 418).pointIds 418)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M8300_8500.SplitData.node0095 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0096
  · rfl
  · rfl
  · rfl
  · rfl

def B0094 : Block := .branch 162 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 415).pointIds 415), B0095, (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M8300_8500.SplitData.node0094 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0095
  · rfl
  · rfl

def B0093 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 413).pointIds 413), (.leaf 3 (Common.fact 414).pointIds 414), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0094]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M8300_8500.SplitData.node0093 := by
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
  · exact treeEq0094

def B0092 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849533707471873599276111034867720, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 411).pointIds 411), (.leaf 3 (Common.fact 412).pointIds 412), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0093]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M8300_8500.SplitData.node0092 := by
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
  · exact treeEq0093

def B0098 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184345825986482785862521716800] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 413).pointIds 413), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 423).pointIds 423)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M8300_8500.SplitData.node0098 := by
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

def B0066 : Block := .branch 87 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 343).pointIds 343), (.leaf 1 (Common.fact 344).pointIds 344), B0067, B0092, (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), B0098]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M8300_8500.SplitData.node0066 := by
  change Tree.branch (87 : Fin 177) _ = Tree.branch (87 : Fin 177) _
  apply congrArg (Tree.branch (87 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0067
  · exact treeEq0092
  · rfl
  · rfl
  · exact treeEq0098

theorem accepted0066 : B0066.accepted = true := by decide +kernel
theorem checked0066 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0066 (maskNeeds ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272]) := by
  rw [← treeEq0066]
  exact B0066.sound accepted0066
#print axioms checked0066

def Tip0062_0066 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0066 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] checked0066
def B0104 : Block := .branch 171 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 433).pointIds 433), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M8300_8500.SplitData.node0104 := by
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

def B0103 : Block := .branch 170 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 406).pointIds 406), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 431).pointIds 431), (.leaf 4 (Common.fact 375).pointIds 375), (.leaf 5 (Common.fact 376).pointIds 376), B0104]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M8300_8500.SplitData.node0103 := by
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
  · exact treeEq0104

def B0102 : Block := .branch 161 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0103, (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 6 (Common.fact 418).pointIds 418)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M8300_8500.SplitData.node0102 := by
  change Tree.branch (161 : Fin 177) _ = Tree.branch (161 : Fin 177) _
  apply congrArg (Tree.branch (161 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 162 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 355).pointIds 355), (.leaf 1 (Common.fact 356).pointIds 356), (.leaf 2 (Common.fact 357).pointIds 357), (.leaf 3 (Common.fact 428).pointIds 428), B0102, (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M8300_8500.SplitData.node0101 := by
  change Tree.branch (162 : Fin 177) _ = Tree.branch (162 : Fin 177) _
  apply congrArg (Tree.branch (162 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0102
  · rfl
  · rfl

def B0100 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 427).pointIds 427), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), B0101]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M8300_8500.SplitData.node0100 := by
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
  · exact treeEq0101

def B0099 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850542750678201290218029473800, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 425).pointIds 425), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0100]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M8300_8500.SplitData.node0099 := by
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
  · exact treeEq0100

def B0105 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184268454734027449595340521536] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), (.leaf 6 (Common.fact 434).pointIds 434)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M8300_8500.SplitData.node0105 := by
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
  · rfl

def B0065 : Block := .branch 86 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 58460065493236116728147393308651320786237301817360, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), Tip0062_0066, B0099, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B0105]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M8300_8500.SplitData.node0065 := by
  change Tree.branch (86 : Fin 177) _ = Tree.branch (86 : Fin 177) _
  apply congrArg (Tree.branch (86 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0099
  · rfl
  · rfl
  · exact treeEq0105

def B0109 : Block := .branch 171 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 46773761428958395483787388422043726186730674847776, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 390).pointIds 390), (.leaf 4 (Common.fact 441).pointIds 441), (.leaf 5 (Common.fact 442).pointIds 442), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M8300_8500.SplitData.node0109 := by
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

def B0108 : Block := .branch 170 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 46773761428958395483787388422043726186730674847776, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 371).pointIds 371), (.leaf 1 (Common.fact 406).pointIds 406), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 388).pointIds 388), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), B0109]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M8300_8500.SplitData.node0108 := by
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
  · exact treeEq0109

def B0107 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 46773761428958395483787388422043726186730674847776, 374144419156711147060143317175368453032468486291520] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 386).pointIds 386), (.leaf 4 (Common.fact 437).pointIds 437), (.leaf 5 (Common.fact 438).pointIds 438), B0108]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M8300_8500.SplitData.node0107 := by
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
  · exact treeEq0108

def B0106 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 46773761428958395483787388422043726186730674847776, 549755289664] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 436).pointIds 436), B0107]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M8300_8500.SplitData.node0106 := by
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
  · exact treeEq0107

def B0064 : Block := .branch 165 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551429937849850465379425745953950848278536, 12057388507979949075180399869909334912161443577872, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 335).pointIds 335), (.leaf 1 (Common.fact 336).pointIds 336), (.leaf 2 (Common.fact 337).pointIds 337), (.leaf 3 (Common.fact 338).pointIds 338), B0065, B0106, (.leaf 0 [] 0)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M8300_8500.SplitData.node0064 := by
  change Tree.branch (165 : Fin 177) _ = Tree.branch (165 : Fin 177) _
  apply congrArg (Tree.branch (165 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · exact treeEq0106
  · rfl

def B0111 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949075180399869909334912161443577872, 5709034369502101269473775122669557740833472544, 374144430307083746325771800593284646707023415083072] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 437).pointIds 437), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 445).pointIds 445)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M8300_8500.SplitData.node0111 := by
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

def B0110 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949075180399869909334912161443577872, 5709034369502101269473775122669557740833472544, 11150372599265628483417916193675104684081216] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 435).pointIds 435), (.leaf 5 (Common.fact 364).pointIds 364), B0111]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M8300_8500.SplitData.node0110 := by
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
  · exact treeEq0111

def B0063 : Block := .branch 98 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949075180399869909334912161443577872, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0064, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), B0110]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M8300_8500.SplitData.node0063 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0064
  · rfl
  · rfl
  · exact treeEq0110

def B0113 : Block := .branch 169 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 385836443405730969671084366604957853513896699625536] ![(.leaf 0 (Common.fact 365).pointIds 365), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 447).pointIds 447), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 448).pointIds 448)]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M8300_8500.SplitData.node0113 := by
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

def B0112 : Block := .branch 168 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11692024249019822610941049429589400481977968623680] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 446).pointIds 446), (.leaf 5 (Common.fact 364).pointIds 364), B0113]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M8300_8500.SplitData.node0112 := by
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
  · exact treeEq0113

def B0062 : Block := .branch 163 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0063, (.leaf 5 (Common.fact 329).pointIds 329), B0112]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M8300_8500.SplitData.node0062 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0063
  · rfl
  · exact treeEq0112

theorem accepted0062 : B0062.accepted = true := by decide +kernel
theorem checked0062 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0062 (maskNeeds ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272]) := by
  rw [← treeEq0062]
  exact B0062.sound accepted0062
#print axioms checked0062

def Tip0059_0062 : Block := .tip HexagonCover.NBand.M8300_8500.SplitData.node0062 ![57115899269183218607248760090132865, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] checked0062
def B0120 : Block := .branch 171 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 2619010934096978029421637045527693285924729223905344] ![(.leaf 0 (Common.fact 462).pointIds 462), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 463).pointIds 463), (.leaf 4 (Common.fact 464).pointIds 464), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M8300_8500.SplitData.node0120 := by
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

def B0119 : Block := .branch 170 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 1122433257470133441181063776826219473797054299897920] ![(.leaf 0 (Common.fact 459).pointIds 459), (.leaf 1 (Common.fact 406).pointIds 406), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 376).pointIds 376), B0120]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M8300_8500.SplitData.node0119 := by
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
  · exact treeEq0120

def B0118 : Block := .branch 98 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949724217507186762788478473484730384, 5709034369502101269473775122669557740833472544, 1122433257470133441181063776826219473797054299897920] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0119, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M8300_8500.SplitData.node0118 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0119
  · rfl
  · rfl
  · rfl

def B0117 : Block := .branch 108 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949724217507186762788478473484730384, 5709034369502101269473775122669557740833472544, 1122433268620506040446375347594078610121235052888128] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0118, (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 457).pointIds 457)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M8300_8500.SplitData.node0117 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0118
  · rfl
  · rfl
  · rfl

def B0116 : Block := .branch 163 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 1122433268620506040446375347594078610121235052888128] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0117, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 451).pointIds 451)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M8300_8500.SplitData.node0116 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0117
  · rfl
  · rfl

def B0115 : Block := .branch 169 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 374144430307083746326088713243341704057397590884416] ![(.leaf 0 (Common.fact 450).pointIds 450), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 447).pointIds 447), (.leaf 5 (Common.fact 370).pointIds 370), B0116]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M8300_8500.SplitData.node0115 := by
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
  · exact treeEq0116

def B0114 : Block := .branch 168 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11150372599265945396067973251025478859882560] ![(.leaf 0 (Common.fact 449).pointIds 449), (.leaf 1 (Common.fact 402).pointIds 402), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 446).pointIds 446), (.leaf 5 (Common.fact 364).pointIds 364), B0115]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M8300_8500.SplitData.node0114 := by
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
  · exact treeEq0115

def B0061 : Block := .branch 99 ![57115266062853124135238149188092289, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![Tip0059_0062, (.leaf 1 (Common.fact 320).pointIds 320), (.leaf 2 (Common.fact 321).pointIds 321), (.leaf 3 (Common.fact 322).pointIds 322), (.leaf 4 (Common.fact 323).pointIds 323), (.leaf 5 (Common.fact 324).pointIds 324), B0114]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M8300_8500.SplitData.node0061 := by
  change Tree.branch (99 : Fin 177) _ = Tree.branch (99 : Fin 177) _
  apply congrArg (Tree.branch (99 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0114

def B0121 : Block := .branch 169 ![57116533094785564176853165735412097, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184810053501214803465608888384] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 404).pointIds 404), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 447).pointIds 447), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 467).pointIds 467)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M8300_8500.SplitData.node0121 := by
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

def B0060 : Block := .branch 89 ![57116533094785564176853165735412097, 730750818665451459101842416358141510377722086914, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![B0061, (.leaf 1 (Common.fact 315).pointIds 315), (.leaf 2 (Common.fact 316).pointIds 316), (.leaf 3 (Common.fact 317).pointIds 317), (.leaf 4 (Common.fact 318).pointIds 318), (.leaf 5 (Common.fact 319).pointIds 319), B0121]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M8300_8500.SplitData.node0060 := by
  change Tree.branch (89 : Fin 177) _ = Tree.branch (89 : Fin 177) _
  apply congrArg (Tree.branch (89 : Fin 177))
  funext i
  fin_cases i
  · exact treeEq0061
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0121

def B0128 : Block := .branch 171 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 2619010934096978029421003220227579171223980872302656] ![(.leaf 0 (Common.fact 476).pointIds 476), (.leaf 1 (Common.fact 477).pointIds 477), (.leaf 2 (Common.fact 432).pointIds 432), (.leaf 3 (Common.fact 463).pointIds 463), (.leaf 4 (Common.fact 464).pointIds 464), (.leaf 5 (Common.fact 382).pointIds 382), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M8300_8500.SplitData.node0128 := by
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

def B0127 : Block := .branch 170 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 474).pointIds 474), (.leaf 1 (Common.fact 475).pointIds 475), (.leaf 2 (Common.fact 430).pointIds 430), (.leaf 3 (Common.fact 460).pointIds 460), (.leaf 4 (Common.fact 461).pointIds 461), (.leaf 5 (Common.fact 376).pointIds 376), B0128]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M8300_8500.SplitData.node0127 := by
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
  · exact treeEq0128

def B0126 : Block := .branch 98 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949724217507186762788478473484730384, 5709034369502101269473775122669557740833472544, 1122433257470133441180429951526105359096305948295232] ![(.leaf 0 (Common.fact 330).pointIds 330), (.leaf 1 (Common.fact 331).pointIds 331), (.leaf 2 (Common.fact 332).pointIds 332), B0127, (.leaf 4 (Common.fact 333).pointIds 333), (.leaf 5 (Common.fact 334).pointIds 334), (.leaf 6 (Common.fact 473).pointIds 473)]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M8300_8500.SplitData.node0126 := by
  change Tree.branch (98 : Fin 177) _ = Tree.branch (98 : Fin 177) _
  apply congrArg (Tree.branch (98 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0127
  · rfl
  · rfl
  · rfl

def B0125 : Block := .branch 108 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 12057388507979949724217507186762788478473484730384, 5709034369502101269473775122669557740833472544, 1122433268620506040445741522293964495420486701285440] ![(.leaf 0 (Common.fact 452).pointIds 452), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), B0126, (.leaf 4 (Common.fact 455).pointIds 455), (.leaf 5 (Common.fact 456).pointIds 456), (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M8300_8500.SplitData.node0125 := by
  change Tree.branch (108 : Fin 177) _ = Tree.branch (108 : Fin 177) _
  apply congrArg (Tree.branch (108 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0126
  · rfl
  · rfl
  · rfl

def B0124 : Block := .branch 163 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 1122433268620506040445741522293964495420486701285440] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), (.leaf 2 (Common.fact 327).pointIds 327), (.leaf 3 (Common.fact 328).pointIds 328), B0125, (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M8300_8500.SplitData.node0124 := by
  change Tree.branch (163 : Fin 177) _ = Tree.branch (163 : Fin 177) _
  apply congrArg (Tree.branch (163 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0125
  · rfl
  · rfl

def B0123 : Block := .branch 169 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 374144430307083746325454887943227589356649239281728] ![(.leaf 0 (Common.fact 466).pointIds 466), (.leaf 1 (Common.fact 470).pointIds 470), (.leaf 2 (Common.fact 426).pointIds 426), (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 447).pointIds 447), (.leaf 5 (Common.fact 370).pointIds 370), B0124]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M8300_8500.SplitData.node0123 := by
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
  · exact treeEq0124

def B0122 : Block := .branch 168 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11150372599265311570767859136324730508279872] ![(.leaf 0 (Common.fact 468).pointIds 468), (.leaf 1 (Common.fact 469).pointIds 469), (.leaf 2 (Common.fact 424).pointIds 424), (.leaf 3 (Common.fact 443).pointIds 443), (.leaf 4 (Common.fact 446).pointIds 446), (.leaf 5 (Common.fact 364).pointIds 364), B0123]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M8300_8500.SplitData.node0122 := by
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
  · exact treeEq0123

def B0059 : Block := .branch 159 ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272] ![(.leaf 0 (Common.fact 310).pointIds 310), B0060, (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B0122]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M8300_8500.SplitData.node0059 := by
  change Tree.branch (159 : Fin 177) _ = Tree.branch (159 : Fin 177) _
  apply congrArg (Tree.branch (159 : Fin 177))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0060
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0122

theorem accepted0059 : B0059.accepted = true := by decide +kernel
theorem checked0059 : CheckedWith (fun (_ : Fin 177) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8300_8500.SplitData.node0059 (maskNeeds ![57116533094785564176853165735412097, 226673591178292726072834, 53230514994906640848787460, 89551430602463689901512333669182293900550152, 365375409332726378588028525032524321226024386576, 5709034369502101269473775122669557740833472544, 11172171938396184191083481572113328159326272]) := by
  rw [← treeEq0059]
  exact B0059.sound accepted0059
#print axioms checked0059

end HexagonCover.NBand.M8300_8500.SplitTree.Run0000
