import HexagonCover.NBand.M8500_8700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M8500_8700.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M8500_8700

abbrev Block := Chunk (n := 175) (Certificate := Fin 1173) (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck

def B0079 : Block := .branch 172 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 2999001449005993582276453842876685846927419602133000, 58460065493236116728147393308651320786237301817360, 748294569604938316490434009030332976692744499363872, 1870722095827111878266596709200154214911409741365312] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 424).pointIds 424), (.leaf 2 (Common.fact 425).pointIds 425), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 428).pointIds 428), (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M8500_8700.SplitData.node0079 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0078 : Block := .branch 171 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 748294569604938316490434009030332976692744499363872, 1870722095827111878266596709200154214911409741365312] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 418).pointIds 418), (.leaf 2 (Common.fact 419).pointIds 419), B0079, (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 421).pointIds 421), (.leaf 6 (Common.fact 422).pointIds 422)]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M8500_8700.SplitData.node0078 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0079
  · rfl
  · rfl
  · rfl

def B0077 : Block := .branch 170 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 748294569604938316490434009030332976692744499363872, 374144419200267290026023440498680402783734817357888] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), (.leaf 2 (Common.fact 413).pointIds 413), (.leaf 3 (Common.fact 414).pointIds 414), (.leaf 4 (Common.fact 415).pointIds 415), (.leaf 5 (Common.fact 416).pointIds 416), B0078]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M8500_8700.SplitData.node0077 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0078

def B0081 : Block := .branch 172 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 2999001449005993582276453842876685846927419602133000, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 748288849507351036351478328441907992139834301349952] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 424).pointIds 424), (.leaf 2 (Common.fact 425).pointIds 425), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 433).pointIds 433)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M8500_8700.SplitData.node0081 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 171 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 748288849507351036351478328441907992139834301349952] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 418).pointIds 418), (.leaf 2 (Common.fact 419).pointIds 419), B0081, (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 430).pointIds 430), (.leaf 6 (Common.fact 431).pointIds 431)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M8500_8700.SplitData.node0080 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0081
  · rfl
  · rfl
  · rfl

def B0076 : Block := .branch 169 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 407).pointIds 407), (.leaf 2 (Common.fact 408).pointIds 408), (.leaf 3 (Common.fact 409).pointIds 409), (.leaf 4 (Common.fact 410).pointIds 410), B0077, B0080]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M8500_8700.SplitData.node0076 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0077
  · exact treeEq0080

def B0075 : Block := .branch 168 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 2923003274661805836407374501135844497828563916804, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 401).pointIds 401), (.leaf 2 (Common.fact 402).pointIds 402), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 404).pointIds 404), (.leaf 5 (Common.fact 405).pointIds 405), B0076]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M8500_8700.SplitData.node0075 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0076

def B0085 : Block := .branch 169 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 8769099026966211631714675139170788711381619204104, 58460065493236116728147393308651320786237301817360, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 407).pointIds 407), (.leaf 2 (Common.fact 441).pointIds 441), (.leaf 3 (Common.fact 442).pointIds 442), (.leaf 4 (Common.fact 410).pointIds 410), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M8500_8700.SplitData.node0085 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 170 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 8769099026966211631714675139170788711381619204104, 58460065493236116728147393308651320786237301817360, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 439).pointIds 439), (.leaf 4 (Common.fact 415).pointIds 415), B0085, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M8500_8700.SplitData.node0084 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0085
  · rfl

def B0083 : Block := .branch 171 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 8769099026966211631714675139170788711381619204104, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 418).pointIds 418), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 437).pointIds 437), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 430).pointIds 430), B0084]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M8500_8700.SplitData.node0083 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0084

def B0082 : Block := .branch 168 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 8769099026966211631714675139170788711381619204104, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 401).pointIds 401), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 435).pointIds 435), (.leaf 4 (Common.fact 404).pointIds 404), (.leaf 5 (Common.fact 405).pointIds 405), B0083]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M8500_8700.SplitData.node0082 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0083

def B0088 : Block := .branch 172 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 2999001449005993582276453842876685846927419602133000, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 424).pointIds 424), (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M8500_8700.SplitData.node0088 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0087 : Block := .branch 171 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 377067433625344230423607498239905026973156406460480] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 418).pointIds 418), (.leaf 2 (Common.fact 436).pointIds 436), B0088, (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 430).pointIds 430), (.leaf 6 (Common.fact 445).pointIds 445)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M8500_8700.SplitData.node0087 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl
  · rfl

def B0086 : Block := .branch 168 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 2923014468633083363464181064536573941237675458624] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 401).pointIds 401), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 404).pointIds 404), (.leaf 5 (Common.fact 405).pointIds 405), B0087]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M8500_8700.SplitData.node0086 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0087

def B0074 : Block := .branch 161 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 396).pointIds 396), (.leaf 1 (Common.fact 397).pointIds 397), B0075, B0082, (.leaf 4 (Common.fact 398).pointIds 398), (.leaf 5 (Common.fact 399).pointIds 399), B0086]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M8500_8700.SplitData.node0074 := by
  change Tree.branch (161 : Fin 175) _ = Tree.branch (161 : Fin 175) _
  apply congrArg (Tree.branch (161 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0075
  · exact treeEq0082
  · rfl
  · rfl
  · exact treeEq0086

theorem accepted0074 : B0074.accepted = true := by decide +kernel
theorem checked0074 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0074 (maskNeeds ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0074]
  exact B0074.sound accepted0074
#print axioms checked0074

def Tip0071_0074 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0074 ![36346711835043908093126774773252481, 2192252455996354377305527249074424530033654629890, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] checked0074
def B0093 : Block := .branch 169 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 457).pointIds 457), (.leaf 2 (Common.fact 458).pointIds 458), (.leaf 3 (Common.fact 409).pointIds 409), (.leaf 4 (Common.fact 410).pointIds 410), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M8500_8700.SplitData.node0093 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 170 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 455).pointIds 455), (.leaf 2 (Common.fact 456).pointIds 456), (.leaf 3 (Common.fact 414).pointIds 414), (.leaf 4 (Common.fact 415).pointIds 415), B0093, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M8500_8700.SplitData.node0092 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0093
  · rfl

def B0091 : Block := .branch 171 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 5992156802259682758757600380279633471182769450147848, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 454).pointIds 454), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 420).pointIds 420), (.leaf 5 (Common.fact 430).pointIds 430), B0092]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M8500_8700.SplitData.node0091 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0092

def B0090 : Block := .branch 172 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 451).pointIds 451), B0091, (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M8500_8700.SplitData.node0090 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0091
  · rfl
  · rfl
  · rfl

def B0089 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 1461501637330902918203689668419561478172631373828, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 404).pointIds 404), (.leaf 5 (Common.fact 405).pointIds 405), B0090]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M8500_8700.SplitData.node0089 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0090

def B0094 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 1461512831302180445260496231820290921581742915648] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 404).pointIds 404), (.leaf 5 (Common.fact 405).pointIds 405), (.leaf 6 (Common.fact 459).pointIds 459)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M8500_8700.SplitData.node0094 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0073 : Block := .branch 160 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 58460065493236116728147393308651320786237301817360, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 392).pointIds 392), Tip0071_0074, B0089, (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 395).pointIds 395), B0094]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M8500_8700.SplitData.node0073 := by
  change Tree.branch (160 : Fin 175) _ = Tree.branch (160 : Fin 175) _
  apply congrArg (Tree.branch (160 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0089
  · rfl
  · rfl
  · rfl
  · exact treeEq0094

def B0099 : Block := .branch 169 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 12057388507979949075180399869909334912161443577872, 1543345729021433481623091183348394868756664765775904, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 457).pointIds 457), (.leaf 2 (Common.fact 441).pointIds 441), (.leaf 3 (Common.fact 409).pointIds 409), (.leaf 4 (Common.fact 467).pointIds 467), (.leaf 5 (Common.fact 468).pointIds 468), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M8500_8700.SplitData.node0099 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 170 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 12057388507979949075180399869909334912161443577872, 46768052394588893382517914646921056628989841768480, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 455).pointIds 455), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 414).pointIds 414), (.leaf 4 (Common.fact 466).pointIds 466), B0099, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M8500_8700.SplitData.node0098 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0099
  · rfl

def B0097 : Block := .branch 171 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5992156802259682758757600380279633471182769450147848, 12057388507979949075180399869909334912161443577872, 46773783686104915752665289326517127257896878735392, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 464).pointIds 464), (.leaf 5 (Common.fact 465).pointIds 465), B0098]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M8500_8700.SplitData.node0097 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0098

def B0096 : Block := .branch 172 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 12057388507979949075180399869909334912161443577872, 46773783686104915752665289326517127257896878735392, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 446).pointIds 446), B0097, (.leaf 4 (Common.fact 462).pointIds 462), (.leaf 5 (Common.fact 463).pointIds 463), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M8500_8700.SplitData.node0096 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0097
  · rfl
  · rfl
  · rfl

def B0095 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 12057388507979949075180399869909334912161443577872, 46773783686104915752665289326517127257896878735392, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 460).pointIds 460), (.leaf 5 (Common.fact 461).pointIds 461), B0096]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M8500_8700.SplitData.node0095 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0096

def B0072 : Block := .branch 165 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 12057388507979949075180399869909334912161443577872, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 388).pointIds 388), (.leaf 1 (Common.fact 389).pointIds 389), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), B0073, B0095, (.leaf 0 [] 0)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M8500_8700.SplitData.node0072 := by
  change Tree.branch (165 : Fin 175) _ = Tree.branch (165 : Fin 175) _
  apply congrArg (Tree.branch (165 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0073
  · exact treeEq0095
  · rfl

def B0104 : Block := .branch 170 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 748294569604938316490434009030332976692744499363872, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 455).pointIds 455), (.leaf 2 (Common.fact 438).pointIds 438), (.leaf 3 (Common.fact 414).pointIds 414), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 416).pointIds 416), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M8500_8700.SplitData.node0104 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0103 : Block := .branch 169 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 457).pointIds 457), (.leaf 2 (Common.fact 441).pointIds 441), (.leaf 3 (Common.fact 409).pointIds 409), (.leaf 4 (Common.fact 473).pointIds 473), B0104, (.leaf 6 (Common.fact 474).pointIds 474)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M8500_8700.SplitData.node0103 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0104
  · rfl

def B0102 : Block := .branch 171 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5992156802259682758757600380279633471182769450147848, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 436).pointIds 436), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 430).pointIds 430), B0103]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M8500_8700.SplitData.node0102 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0103

def B0101 : Block := .branch 172 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 385836443449329647932829607236202725091092001718336] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 446).pointIds 446), B0102, (.leaf 4 (Common.fact 470).pointIds 470), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 471).pointIds 471)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M8500_8700.SplitData.node0101 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0102
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11692024292618500872686290060834272059173270716480] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 434).pointIds 434), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 405).pointIds 405), B0101]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M8500_8700.SplitData.node0100 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0101

def B0071 : Block := .branch 163 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), B0072, (.leaf 5 (Common.fact 387).pointIds 387), B0100]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M8500_8700.SplitData.node0071 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0072
  · rfl
  · exact treeEq0100

theorem accepted0071 : B0071.accepted = true := by decide +kernel
theorem checked0071 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0071 (maskNeeds ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672]) := by
  rw [← treeEq0071]
  exact B0071.sound accepted0071
#print axioms checked0071

def Tip0068_0071 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0071 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 169249614746048084458870788, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] checked0071
def B0107 : Block := .branch 172 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 2999001449005993582276453842876685846927419602133000, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056966141608918574460172763200] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 470).pointIds 470), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 481).pointIds 481)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M8500_8700.SplitData.node0107 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0106 : Block := .branch 171 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 374144430350682424587200283316977371606378903765056] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 478).pointIds 478), B0107, (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 430).pointIds 430), (.leaf 6 (Common.fact 479).pointIds 479)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M8500_8700.SplitData.node0106 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0107
  · rfl
  · rfl
  · rfl

def B0105 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056966141608918574460172763200] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 403).pointIds 403), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 405).pointIds 405), B0106]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M8500_8700.SplitData.node0105 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0106

def B0070 : Block := .branch 87 ![36346711835043908093126774773252481, 730750818665451459101842567473868962206368925186, 130601767450242908029982724, 5846095752304405795307305473738222672069754118152, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527056811399104007901925810372672] ![(.leaf 0 (Common.fact 378).pointIds 378), (.leaf 1 (Common.fact 379).pointIds 379), Tip0068_0071, (.leaf 3 (Common.fact 380).pointIds 380), (.leaf 4 (Common.fact 381).pointIds 381), (.leaf 5 (Common.fact 382).pointIds 382), B0105]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M8500_8700.SplitData.node0070 := by
  change Tree.branch (87 : Fin 175) _ = Tree.branch (87 : Fin 175) _
  apply congrArg (Tree.branch (87 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0105

def B0112 : Block := .branch 169 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6211381958656337402365660539044202833537713405968, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 406).pointIds 406), (.leaf 1 (Common.fact 457).pointIds 457), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 492).pointIds 492), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M8500_8700.SplitData.node0112 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0111 : Block := .branch 170 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6211381958656337402365660539044202833537713405968, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 455).pointIds 455), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 489).pointIds 489), B0112, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M8500_8700.SplitData.node0111 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0112
  · rfl

def B0110 : Block := .branch 171 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 5986310796058808290812143540185320994464650544308232, 6211381958656337402365660539044202833537713405968, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 417).pointIds 417), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 486).pointIds 486), (.leaf 5 (Common.fact 430).pointIds 430), B0111]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M8500_8700.SplitData.node0110 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0111

def B0109 : Block := .branch 172 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6211381958656337402365660539044202833537713405968, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 423).pointIds 423), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 480).pointIds 480), B0110, (.leaf 4 (Common.fact 484).pointIds 484), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M8500_8700.SplitData.node0109 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0110
  · rfl
  · rfl
  · rfl

def B0108 : Block := .branch 168 ![36346711835043908093126774773252481, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 6211381958656337402365660539044202833537713405968, 5731291516022370147374679596070628907037360160, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 400).pointIds 400), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 483).pointIds 483), (.leaf 5 (Common.fact 405).pointIds 405), B0109]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M8500_8700.SplitData.node0108 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0109

def B0069 : Block := .branch 162 ![36346711835043908093126774773252481, 730750818665451459101842567473868962206368925186, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 373).pointIds 373), (.leaf 1 (Common.fact 374).pointIds 374), (.leaf 2 (Common.fact 375).pointIds 375), B0070, B0108, (.leaf 5 (Common.fact 376).pointIds 376), (.leaf 6 (Common.fact 377).pointIds 377)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M8500_8700.SplitData.node0069 := by
  change Tree.branch (162 : Fin 175) _ = Tree.branch (162 : Fin 175) _
  apply congrArg (Tree.branch (162 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0070
  · exact treeEq0108
  · rfl
  · rfl

def B0117 : Block := .branch 169 ![36346078628713813621116163871211905, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 1496577676626844588240573268701473812127674924400672, 3367299783604329065773115373969601278064013769965632] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 457).pointIds 457), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 473).pointIds 473), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 500).pointIds 500)]
theorem treeEq0117 : B0117.tree = HexagonCover.NBand.M8500_8700.SplitData.node0117 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0116 : Block := .branch 170 ![36346078628713813621116163871211905, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 393248, 3367299783604329065773115373969601278064013769965632] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 455).pointIds 455), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 475).pointIds 475), B0117, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0116 : B0116.tree = HexagonCover.NBand.M8500_8700.SplitData.node0116 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0117
  · rfl

def B0115 : Block := .branch 171 ![36346078628713813621116163871211905, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 5986310796058808290812143540185320994464650544308232, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 374144430350639889291968836566653653808663921950784] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 453).pointIds 453), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 430).pointIds 430), B0116]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M8500_8700.SplitData.node0115 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0116

def B0114 : Block := .branch 172 ![36346078628713813621116163871211905, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 374144430350682424587833953874586575634592892977216] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 450).pointIds 450), (.leaf 2 (Common.fact 480).pointIds 480), B0115, (.leaf 4 (Common.fact 470).pointIds 470), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M8500_8700.SplitData.node0114 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0115
  · rfl
  · rfl
  · rfl

def B0113 : Block := .branch 168 ![36346078628713813621116163871211905, 730750818665451459101842416358141510377722086914, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11193971277527690636699218122602674161975360] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 448).pointIds 448), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 405).pointIds 405), B0114]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M8500_8700.SplitData.node0113 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0114

def B0068 : Block := .branch 99 ![36346078628713813621116163871211905, 730750818665451459101842567473868962206368925186, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448] ![B0069, (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 369).pointIds 369), (.leaf 3 (Common.fact 370).pointIds 370), (.leaf 4 (Common.fact 371).pointIds 371), (.leaf 5 (Common.fact 372).pointIds 372), B0113]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M8500_8700.SplitData.node0068 := by
  change Tree.branch (99 : Fin 175) _ = Tree.branch (99 : Fin 175) _
  apply congrArg (Tree.branch (99 : Fin 175))
  funext i
  fin_cases i
  · exact treeEq0069
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0113

theorem accepted0068 : B0068.accepted = true := by decide +kernel
theorem checked0068 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0068 (maskNeeds ![36346078628713813621116163871211905, 730750818665451459101842567473868962206368925186, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0068]
  exact B0068.sound accepted0068
#print axioms checked0068

def Tip0065_0068 : Block := .tip HexagonCover.NBand.M8500_8700.SplitData.node0068 ![36346078628713813621116163871211905, 730750818665451459101842567473868962206368925186, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448] checked0068
def B0122 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 1496577676626844588240573268701473812127674924400672, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 473).pointIds 473), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0122 : B0122.tree = HexagonCover.NBand.M8500_8700.SplitData.node0122 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0121 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 393248, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 475).pointIds 475), B0122, (.leaf 6 (Common.fact 440).pointIds 440)]
theorem treeEq0121 : B0121.tree = HexagonCover.NBand.M8500_8700.SplitData.node0121 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0122
  · rfl

def B0120 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310796058808290812143540185320994464650544308232, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 472).pointIds 472), (.leaf 5 (Common.fact 430).pointIds 430), B0121]
theorem treeEq0120 : B0120.tree = HexagonCover.NBand.M8500_8700.SplitData.node0120 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0121

def B0119 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 374875181169347876046301970990830602443672507646016] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0120, (.leaf 4 (Common.fact 470).pointIds 470), (.leaf 5 (Common.fact 432).pointIds 432), (.leaf 6 (Common.fact 503).pointIds 503)]
theorem treeEq0119 : B0119.tree = HexagonCover.NBand.M8500_8700.SplitData.node0119 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0120
  · rfl
  · rfl
  · rfl

def B0118 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 730762012636728986158653815462149411753776644160] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 469).pointIds 469), (.leaf 5 (Common.fact 405).pointIds 405), B0119]
theorem treeEq0118 : B0118.tree = HexagonCover.NBand.M8500_8700.SplitData.node0118 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0119

def B0067 : Block := .branch 159 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 365375409332726378588028525032524321226024386576, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 363).pointIds 363), Tip0065_0068, (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 366).pointIds 366), (.leaf 5 (Common.fact 367).pointIds 367), B0118]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M8500_8700.SplitData.node0067 := by
  change Tree.branch (159 : Fin 175) _ = Tree.branch (159 : Fin 175) _
  apply congrArg (Tree.branch (159 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0118

def B0126 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2854495385412568799223888792352556584806744080, 365397710077924260174062743897343403275489509408, 3367299783604329065772481548669487163363265418362944] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 513).pointIds 513), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0126 : B0126.tree = HexagonCover.NBand.M8500_8700.SplitData.node0126 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0125 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 5986310796058808290812143540185320994464650544308232, 2854495385412568799223888792352556584806744080, 365397710077924260174062743897343403275489509408, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), (.leaf 3 (Common.fact 485).pointIds 485), (.leaf 4 (Common.fact 511).pointIds 511), (.leaf 5 (Common.fact 512).pointIds 512), B0126]
theorem treeEq0125 : B0125.tree = HexagonCover.NBand.M8500_8700.SplitData.node0125 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0126

def B0124 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2854495385412568799223888792352556584806744080, 365397710077924260174062743897343403275489509408, 374144430350639889291335011266539539107915570348096] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), B0125, (.leaf 4 (Common.fact 509).pointIds 509), (.leaf 5 (Common.fact 510).pointIds 510), (.leaf 6 (Common.fact 452).pointIds 452)]
theorem treeEq0124 : B0124.tree = HexagonCover.NBand.M8500_8700.SplitData.node0124 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0125
  · rfl
  · rfl
  · rfl

def B0123 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2854495385412568799223888792352556584806744080, 365397710077924260174062743897343403275489509408, 11193928742231191694091171086075996839346240] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 507).pointIds 507), (.leaf 5 (Common.fact 508).pointIds 508), B0124]
theorem treeEq0123 : B0123.tree = HexagonCover.NBand.M8500_8700.SplitData.node0123 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0124

def B0066 : Block := .branch 158 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2854495385412568799223888792352556584806744080, 5731291516022370147374679596070628907037360160, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B0067, B0123, (.leaf 0 [] 0)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M8500_8700.SplitData.node0066 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0067
  · exact treeEq0123
  · rfl

def B0133 : Block := .branch 172 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 2993155442456669970603639103545820714848795871961096, 11694867594032635265391595233669163147520225935376, 22300745198530623141535718272648361506373664, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 494).pointIds 494), (.leaf 1 (Common.fact 502).pointIds 502), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 525).pointIds 525), (.leaf 4 (Common.fact 526).pointIds 526), (.leaf 5 (Common.fact 527).pointIds 527), (.leaf 6 (Common.fact 528).pointIds 528)]
theorem treeEq0133 : B0133.tree = HexagonCover.NBand.M8500_8700.SplitData.node0133 := by
  change Tree.branch (172 : Fin 175) _ = Tree.branch (172 : Fin 175) _
  apply congrArg (Tree.branch (172 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0132 : Block := .branch 171 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89202980794122492566142873090593446023946248, 11694867594032635265391595233669163147520225935376, 22300745198530623141535718272648361506373664, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 496).pointIds 496), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 478).pointIds 478), B0133, (.leaf 4 (Common.fact 522).pointIds 522), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 524).pointIds 524)]
theorem treeEq0132 : B0132.tree = HexagonCover.NBand.M8500_8700.SplitData.node0132 := by
  change Tree.branch (171 : Fin 175) _ = Tree.branch (171 : Fin 175) _
  apply congrArg (Tree.branch (171 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0133
  · rfl
  · rfl
  · rfl

def B0131 : Block := .branch 158 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89202980794122492566142873090593446023946248, 11694867594032635265391595233669163147520225935376, 748288860614167492650909775886455178712198968377376, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 359).pointIds 359), (.leaf 1 (Common.fact 360).pointIds 360), (.leaf 2 (Common.fact 361).pointIds 361), (.leaf 3 (Common.fact 362).pointIds 362), B0132, (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 0 [] 0)]
theorem treeEq0131 : B0131.tree = HexagonCover.NBand.M8500_8700.SplitData.node0131 := by
  change Tree.branch (158 : Fin 175) _ = Tree.branch (158 : Fin 175) _
  apply congrArg (Tree.branch (158 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0132
  · rfl
  · rfl

def B0130 : Block := .branch 170 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 11694867594032635265391595233669163147520225935376, 748288860614167492650909775886455178712198968377376, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 497).pointIds 497), (.leaf 1 (Common.fact 505).pointIds 505), (.leaf 2 (Common.fact 487).pointIds 487), (.leaf 3 (Common.fact 488).pointIds 488), (.leaf 4 (Common.fact 520).pointIds 520), (.leaf 5 (Common.fact 521).pointIds 521), B0131]
theorem treeEq0130 : B0130.tree = HexagonCover.NBand.M8500_8700.SplitData.node0130 := by
  change Tree.branch (170 : Fin 175) _ = Tree.branch (170 : Fin 175) _
  apply congrArg (Tree.branch (170 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0131

def B0129 : Block := .branch 169 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 11694867594032635265391595233669163147520225935376, 22300745198530623141535718272648361506373664, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 499).pointIds 499), (.leaf 1 (Common.fact 506).pointIds 506), (.leaf 2 (Common.fact 490).pointIds 490), (.leaf 3 (Common.fact 491).pointIds 491), (.leaf 4 (Common.fact 518).pointIds 518), B0130, (.leaf 6 (Common.fact 519).pointIds 519)]
theorem treeEq0129 : B0129.tree = HexagonCover.NBand.M8500_8700.SplitData.node0129 := by
  change Tree.branch (169 : Fin 175) _ = Tree.branch (169 : Fin 175) _
  apply congrArg (Tree.branch (169 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0130
  · rfl

def B0128 : Block := .branch 168 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 11694867594032635265391595233669163147520225935376, 22300745198530623141535718272648361506373664, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 493).pointIds 493), (.leaf 1 (Common.fact 501).pointIds 501), (.leaf 2 (Common.fact 477).pointIds 477), (.leaf 3 (Common.fact 482).pointIds 482), (.leaf 4 (Common.fact 516).pointIds 516), (.leaf 5 (Common.fact 517).pointIds 517), B0129]
theorem treeEq0128 : B0128.tree = HexagonCover.NBand.M8500_8700.SplitData.node0128 := by
  change Tree.branch (168 : Fin 175) _ = Tree.branch (168 : Fin 175) _
  apply congrArg (Tree.branch (168 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129

def B0127 : Block := .branch 163 ![36346078628713813621116163871211905, 309485009821345618480596482, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2854495385411919762116571938898990272765591568, 22300745198530623141535718272648361506373664, 5708990813359135389350451810719807024257302592] ![(.leaf 0 (Common.fact 383).pointIds 383), (.leaf 1 (Common.fact 384).pointIds 384), (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 386).pointIds 386), B0128, (.leaf 5 (Common.fact 387).pointIds 387), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0127 : B0127.tree = HexagonCover.NBand.M8500_8700.SplitData.node0127 := by
  change Tree.branch (163 : Fin 175) _ = Tree.branch (163 : Fin 175) _
  apply congrArg (Tree.branch (163 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0128
  · rfl
  · rfl

def B0065 : Block := .branch 152 ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2855889181987476963170234774744597107400867856, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448] ![(.leaf 0 (Common.fact 354).pointIds 354), (.leaf 1 (Common.fact 355).pointIds 355), (.leaf 2 (Common.fact 356).pointIds 356), (.leaf 3 (Common.fact 357).pointIds 357), (.leaf 4 (Common.fact 358).pointIds 358), B0066, B0127]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M8500_8700.SplitData.node0065 := by
  change Tree.branch (152 : Fin 175) _ = Tree.branch (152 : Fin 175) _
  apply congrArg (Tree.branch (152 : Fin 175))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0066
  · exact treeEq0127

theorem accepted0065 : B0065.accepted = true := by decide +kernel
theorem checked0065 : CheckedWith (fun (_ : Fin 175) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M8500_8700.SplitData.node0065 (maskNeeds ![36346078628713813621116163871211905, 309636125548797447127434754, 130601767450242908029982724, 89551429937849850465379425745953950848278536, 2855889181987476963170234774744597107400867856, 22300745198530623141535718272648361506373664, 11226638384751466903891587970215375558672448]) := by
  rw [← treeEq0065]
  exact B0065.sound accepted0065
#print axioms checked0065

end HexagonCover.NBand.M8500_8700.SplitTree.Run0000
