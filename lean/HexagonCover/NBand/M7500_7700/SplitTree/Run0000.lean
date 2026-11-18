import HexagonCover.NBand.M7500_7700.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7500_7700.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M7500_7700

abbrev Block := Chunk (n := 173) (Certificate := Fin 1005) (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck

def B0088 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 383).pointIds 383), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 385).pointIds 385), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M7500_7700.SplitData.node0088 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0089 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 383).pointIds 383), (.leaf 3 (Common.fact 384).pointIds 384), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M7500_7700.SplitData.node0089 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0087 : Block := .branch 165 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), B0088, B0089, (.leaf 0 [] 0)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M7500_7700.SplitData.node0087 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · exact treeEq0089
  · rfl

def B0090 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 383).pointIds 383), (.leaf 3 (Common.fact 390).pointIds 390), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M7500_7700.SplitData.node0090 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0086 : Block := .branch 162 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0087, B0090, (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 376).pointIds 376)]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M7500_7700.SplitData.node0086 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0087
  · exact treeEq0090
  · rfl
  · rfl

def B0091 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 392).pointIds 392), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M7500_7700.SplitData.node0091 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0085 : Block := .branch 161 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), B0086, B0091, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 371).pointIds 371)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M7500_7700.SplitData.node0085 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0086
  · exact treeEq0091
  · rfl
  · rfl
  · rfl

def B0096 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 396).pointIds 396), (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 398).pointIds 398), (.leaf 4 (Common.fact 399).pointIds 399), (.leaf 5 (Common.fact 400).pointIds 400), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M7500_7700.SplitData.node0096 := by
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

def B0097 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 396).pointIds 396), (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 398).pointIds 398), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M7500_7700.SplitData.node0097 := by
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

def B0095 : Block := .branch 165 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), B0096, B0097, (.leaf 0 [] 0)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M7500_7700.SplitData.node0095 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0096
  · exact treeEq0097
  · rfl

def B0098 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 396).pointIds 396), (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 404).pointIds 404), (.leaf 4 (Common.fact 405).pointIds 405), (.leaf 5 (Common.fact 400).pointIds 400), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M7500_7700.SplitData.node0098 := by
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

def B0094 : Block := .branch 162 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0095, B0098, (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 376).pointIds 376)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M7500_7700.SplitData.node0094 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0095
  · exact treeEq0098
  · rfl
  · rfl

def B0099 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 396).pointIds 396), (.leaf 2 (Common.fact 406).pointIds 406), (.leaf 3 (Common.fact 407).pointIds 407), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 400).pointIds 400), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M7500_7700.SplitData.node0099 := by
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

def B0093 : Block := .branch 161 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), B0094, B0099, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 371).pointIds 371)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M7500_7700.SplitData.node0093 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0094
  · exact treeEq0099
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 168 ![604463486268066890776961, 151115727451828646839810, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 381).pointIds 381), B0093, (.leaf 2 (Common.fact 394).pointIds 394), (.leaf 3 (Common.fact 390).pointIds 390), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M7500_7700.SplitData.node0092 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0093
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0084 : Block := .branch 160 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 362).pointIds 362), B0085, B0092, (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 366).pointIds 366)]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M7500_7700.SplitData.node0084 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0085
  · exact treeEq0092
  · rfl
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 400).pointIds 400), (.leaf 6 (Common.fact 411).pointIds 411)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M7500_7700.SplitData.node0100 := by
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

def B0083 : Block := .branch 86 ![604463486268066890776961, 453347182355485940516354, 77937529740219874547716, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 357).pointIds 357), (.leaf 1 (Common.fact 358).pointIds 358), (.leaf 2 (Common.fact 359).pointIds 359), B0084, (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), B0100]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M7500_7700.SplitData.node0083 := by
  change Tree.branch (86 : Fin 173) _ = Tree.branch (86 : Fin 173) _
  apply congrArg (Tree.branch (86 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0084
  · rfl
  · rfl
  · exact treeEq0100

theorem accepted0083 : B0083.accepted = true := by decide +kernel
theorem checked0083 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0083 (maskNeeds ![604463486268066890776961, 453347182355485940516354, 77937529740219874547716, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416]) := by
  rw [← treeEq0083]
  exact B0083.sound accepted0083
#print axioms checked0083

def Tip0078_0083 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0083 ![604463486268066890776961, 453347182355485940516354, 77937529740219874547716, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] checked0083
def B0103 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 414).pointIds 414), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M7500_7700.SplitData.node0103 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0102 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 362).pointIds 362), B0103, (.leaf 2 (Common.fact 413).pointIds 413), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 366).pointIds 366)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M7500_7700.SplitData.node0102 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 412).pointIds 412), B0102, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 371).pointIds 371)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M7500_7700.SplitData.node0101 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0102
  · rfl
  · rfl
  · rfl

def B0082 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 77937529740219874547716, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 352).pointIds 352), Tip0078_0083, B0101, (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M7500_7700.SplitData.node0082 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0101
  · rfl
  · rfl
  · rfl
  · rfl

def B0107 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 395).pointIds 395), (.leaf 1 (Common.fact 408).pointIds 408), (.leaf 2 (Common.fact 418).pointIds 418), (.leaf 3 (Common.fact 419).pointIds 419), (.leaf 4 (Common.fact 405).pointIds 405), (.leaf 5 (Common.fact 400).pointIds 400), (.leaf 6 (Common.fact 401).pointIds 401)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M7500_7700.SplitData.node0107 := by
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

def B0106 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 352).pointIds 352), B0107, (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 353).pointIds 353), (.leaf 4 (Common.fact 354).pointIds 354), (.leaf 5 (Common.fact 355).pointIds 355), (.leaf 6 (Common.fact 356).pointIds 356)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M7500_7700.SplitData.node0106 := by
  change Tree.branch (77 : Fin 173) _ = Tree.branch (77 : Fin 173) _
  apply congrArg (Tree.branch (77 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0107
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0105 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), B0106, (.leaf 3 (Common.fact 416).pointIds 416), (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 371).pointIds 371)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M7500_7700.SplitData.node0105 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0106
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 162 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), (.leaf 3 (Common.fact 415).pointIds 415), B0105, (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 376).pointIds 376)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M7500_7700.SplitData.node0104 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0105
  · rfl
  · rfl

def B0081 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), B0082, B0104, (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M7500_7700.SplitData.node0081 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0082
  · exact treeEq0104
  · rfl
  · rfl
  · rfl

def B0115 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 381).pointIds 381), (.leaf 1 (Common.fact 382).pointIds 382), (.leaf 2 (Common.fact 447).pointIds 447), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 386).pointIds 386), (.leaf 6 (Common.fact 387).pointIds 387)]
theorem treeEq0115 : B0115.tree = HexagonCover.NBand.M7500_7700.SplitData.node0115 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0114 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 362).pointIds 362), B0115, (.leaf 2 (Common.fact 446).pointIds 446), (.leaf 3 (Common.fact 363).pointIds 363), (.leaf 4 (Common.fact 364).pointIds 364), (.leaf 5 (Common.fact 365).pointIds 365), (.leaf 6 (Common.fact 366).pointIds 366)]
theorem treeEq0114 : B0114.tree = HexagonCover.NBand.M7500_7700.SplitData.node0114 := by
  change Tree.branch (160 : Fin 173) _ = Tree.branch (160 : Fin 173) _
  apply congrArg (Tree.branch (160 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0115
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0113 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 348).pointIds 348), (.leaf 1 (Common.fact 349).pointIds 349), B0114, (.leaf 3 (Common.fact 445).pointIds 445), (.leaf 4 (Common.fact 350).pointIds 350), (.leaf 5 (Common.fact 351).pointIds 351), (.leaf 0 [] 0)]
theorem treeEq0113 : B0113.tree = HexagonCover.NBand.M7500_7700.SplitData.node0113 := by
  change Tree.branch (71 : Fin 173) _ = Tree.branch (71 : Fin 173) _
  apply congrArg (Tree.branch (71 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0114
  · rfl
  · rfl
  · rfl
  · rfl

def B0112 : Block := .branch 72 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 439).pointIds 439), (.leaf 1 (Common.fact 440).pointIds 440), B0113, (.leaf 3 (Common.fact 441).pointIds 441), (.leaf 4 (Common.fact 442).pointIds 442), (.leaf 5 (Common.fact 443).pointIds 443), (.leaf 6 (Common.fact 444).pointIds 444)]
theorem treeEq0112 : B0112.tree = HexagonCover.NBand.M7500_7700.SplitData.node0112 := by
  change Tree.branch (72 : Fin 173) _ = Tree.branch (72 : Fin 173) _
  apply congrArg (Tree.branch (72 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0113
  · rfl
  · rfl
  · rfl
  · rfl

def B0111 : Block := .branch 73 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 433).pointIds 433), (.leaf 1 (Common.fact 434).pointIds 434), B0112, (.leaf 3 (Common.fact 435).pointIds 435), (.leaf 4 (Common.fact 436).pointIds 436), (.leaf 5 (Common.fact 437).pointIds 437), (.leaf 6 (Common.fact 438).pointIds 438)]
theorem treeEq0111 : B0111.tree = HexagonCover.NBand.M7500_7700.SplitData.node0111 := by
  change Tree.branch (73 : Fin 173) _ = Tree.branch (73 : Fin 173) _
  apply congrArg (Tree.branch (73 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0112
  · rfl
  · rfl
  · rfl
  · rfl

def B0110 : Block := .branch 74 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517168810704669180640295202545134615396416] ![(.leaf 0 (Common.fact 427).pointIds 427), (.leaf 1 (Common.fact 428).pointIds 428), B0111, (.leaf 3 (Common.fact 429).pointIds 429), (.leaf 4 (Common.fact 430).pointIds 430), (.leaf 5 (Common.fact 431).pointIds 431), (.leaf 6 (Common.fact 432).pointIds 432)]
theorem treeEq0110 : B0110.tree = HexagonCover.NBand.M7500_7700.SplitData.node0110 := by
  change Tree.branch (74 : Fin 173) _ = Tree.branch (74 : Fin 173) _
  apply congrArg (Tree.branch (74 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0111
  · rfl
  · rfl
  · rfl
  · rfl

def B0109 : Block := .branch 75 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078352601739294261663458099100909632] ![(.leaf 0 (Common.fact 421).pointIds 421), (.leaf 1 (Common.fact 422).pointIds 422), B0110, (.leaf 3 (Common.fact 423).pointIds 423), (.leaf 4 (Common.fact 424).pointIds 424), (.leaf 5 (Common.fact 425).pointIds 425), (.leaf 6 (Common.fact 426).pointIds 426)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M7500_7700.SplitData.node0109 := by
  change Tree.branch (75 : Fin 173) _ = Tree.branch (75 : Fin 173) _
  apply congrArg (Tree.branch (75 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0110
  · rfl
  · rfl
  · rfl
  · rfl

def B0108 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078352601739294261663458099100909632] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 420).pointIds 420), B0109, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 371).pointIds 371)]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M7500_7700.SplitData.node0108 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0109
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 66 ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078352601739294261663458099100909632] ![(.leaf 0 (Common.fact 343).pointIds 343), B0081, B0108, (.leaf 3 (Common.fact 344).pointIds 344), (.leaf 4 (Common.fact 345).pointIds 345), (.leaf 5 (Common.fact 346).pointIds 346), (.leaf 6 (Common.fact 347).pointIds 347)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M7500_7700.SplitData.node0080 := by
  change Tree.branch (66 : Fin 173) _ = Tree.branch (66 : Fin 173) _
  apply congrArg (Tree.branch (66 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0081
  · exact treeEq0108
  · rfl
  · rfl
  · rfl
  · rfl

def B0079 : Block := .branch 91 ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078352599263414183092697549302661184] ![(.leaf 0 (Common.fact 337).pointIds 337), (.leaf 1 (Common.fact 338).pointIds 338), (.leaf 2 (Common.fact 339).pointIds 339), (.leaf 3 (Common.fact 340).pointIds 340), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), B0080]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M7500_7700.SplitData.node0079 := by
  change Tree.branch (91 : Fin 173) _ = Tree.branch (91 : Fin 173) _
  apply congrArg (Tree.branch (91 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0080

def B0078 : Block := .branch 102 ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 331).pointIds 331), (.leaf 1 (Common.fact 332).pointIds 332), (.leaf 2 (Common.fact 333).pointIds 333), (.leaf 3 (Common.fact 334).pointIds 334), (.leaf 4 (Common.fact 335).pointIds 335), (.leaf 5 (Common.fact 336).pointIds 336), B0079]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M7500_7700.SplitData.node0078 := by
  change Tree.branch (102 : Fin 173) _ = Tree.branch (102 : Fin 173) _
  apply congrArg (Tree.branch (102 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0079

theorem accepted0078 : B0078.accepted = true := by decide +kernel
theorem checked0078 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0078 (maskNeeds ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680]) := by
  rw [← treeEq0078]
  exact B0078.sound accepted0078
#print axioms checked0078

def Tip0058_0078 : Block := .tip HexagonCover.NBand.M7500_7700.SplitData.node0078 ![604463486268066890776961, 302231454903657293678082, 75576346498785051940868, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680] checked0078
def B0077 : Block := .branch 76 ![604463486268066890776961, 302231526961251331606018, 18482772870728521732, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 325).pointIds 325), (.leaf 1 (Common.fact 326).pointIds 326), Tip0058_0078, (.leaf 3 (Common.fact 327).pointIds 327), (.leaf 4 (Common.fact 328).pointIds 328), (.leaf 5 (Common.fact 329).pointIds 329), (.leaf 6 (Common.fact 330).pointIds 330)]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M7500_7700.SplitData.node0077 := by
  change Tree.branch (76 : Fin 173) _ = Tree.branch (76 : Fin 173) _
  apply congrArg (Tree.branch (76 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0076 : Block := .branch 88 ![604463486268066890776961, 302231526961251331606018, 18482772870728521732, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 200).pointIds 200), (.leaf 1 (Common.fact 201).pointIds 201), (.leaf 2 (Common.fact 202).pointIds 202), (.leaf 3 (Common.fact 203).pointIds 203), (.leaf 4 (Common.fact 204).pointIds 204), (.leaf 5 (Common.fact 205).pointIds 205), B0077]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M7500_7700.SplitData.node0076 := by
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
  · exact treeEq0077

def B0075 : Block := .branch 78 ![604463486268066890776961, 72057594037929474, 18482772870728521732, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 142).pointIds 142), B0076, (.leaf 2 (Common.fact 144).pointIds 144), (.leaf 3 (Common.fact 145).pointIds 145), (.leaf 4 (Common.fact 146).pointIds 146), (.leaf 5 (Common.fact 147).pointIds 147), (.leaf 6 (Common.fact 324).pointIds 324)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M7500_7700.SplitData.node0075 := by
  change Tree.branch (78 : Fin 173) _ = Tree.branch (78 : Fin 173) _
  apply congrArg (Tree.branch (78 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0076
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0074 : Block := .branch 114 ![604463486268066890776961, 72057594037929474, 18482772870728521732, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 323).pointIds 323), (.leaf 1 (Common.fact 183).pointIds 183), (.leaf 2 (Common.fact 184).pointIds 184), (.leaf 3 (Common.fact 185).pointIds 185), (.leaf 4 (Common.fact 186).pointIds 186), B0075, (.leaf 6 (Common.fact 187).pointIds 187)]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M7500_7700.SplitData.node0074 := by
  change Tree.branch (114 : Fin 173) _ = Tree.branch (114 : Fin 173) _
  apply congrArg (Tree.branch (114 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0075
  · rfl

def B0073 : Block := .branch 79 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![B0074, (.leaf 1 (Common.fact 221).pointIds 221), (.leaf 2 (Common.fact 222).pointIds 222), (.leaf 3 (Common.fact 223).pointIds 223), (.leaf 4 (Common.fact 224).pointIds 224), (.leaf 5 (Common.fact 225).pointIds 225), (.leaf 6 (Common.fact 322).pointIds 322)]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M7500_7700.SplitData.node0073 := by
  change Tree.branch (79 : Fin 173) _ = Tree.branch (79 : Fin 173) _
  apply congrArg (Tree.branch (79 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0074
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0072 : Block := .branch 108 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863758235809229933520046342037512, 11874700803313586210404939265819799534704452010000, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), (.leaf 3 (Common.fact 319).pointIds 319), B0073, (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 321).pointIds 321)]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M7500_7700.SplitData.node0072 := by
  change Tree.branch (108 : Fin 173) _ = Tree.branch (108 : Fin 173) _
  apply congrArg (Tree.branch (108 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0073
  · rfl
  · rfl

def B0071 : Block := .branch 119 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863758235809229933520046342037512, 11874700803313586210404939265819799534704452010000, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 154).pointIds 154), (.leaf 1 (Common.fact 155).pointIds 155), (.leaf 2 (Common.fact 156).pointIds 156), (.leaf 3 (Common.fact 157).pointIds 157), B0072, (.leaf 5 (Common.fact 159).pointIds 159), (.leaf 6 (Common.fact 315).pointIds 315)]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M7500_7700.SplitData.node0071 := by
  change Tree.branch (119 : Fin 173) _ = Tree.branch (119 : Fin 173) _
  apply congrArg (Tree.branch (119 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0072
  · rfl
  · rfl

def B0070 : Block := .branch 97 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863599779484201404844859254136840, 11874700803994150944246816192746548749567988432912, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 309).pointIds 309), (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), B0071, (.leaf 4 (Common.fact 312).pointIds 312), (.leaf 5 (Common.fact 313).pointIds 313), (.leaf 6 (Common.fact 314).pointIds 314)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M7500_7700.SplitData.node0070 := by
  change Tree.branch (97 : Fin 173) _ = Tree.branch (97 : Fin 173) _
  apply congrArg (Tree.branch (97 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0071
  · rfl
  · rfl
  · rfl

def B0069 : Block := .branch 107 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863599779484201404844859254136840, 11874700803994150944246816192746548749567988432912, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), B0070, (.leaf 4 (Common.fact 306).pointIds 306), (.leaf 5 (Common.fact 307).pointIds 307), (.leaf 6 (Common.fact 308).pointIds 308)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M7500_7700.SplitData.node0069 := by
  change Tree.branch (107 : Fin 173) _ = Tree.branch (107 : Fin 173) _
  apply congrArg (Tree.branch (107 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0070
  · rfl
  · rfl
  · rfl

def B0068 : Block := .branch 118 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863599779484201404844859254136840, 11874700803994150944246816192746548749567988432912, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), (.leaf 2 (Common.fact 299).pointIds 299), B0069, (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 302).pointIds 302)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M7500_7700.SplitData.node0068 := by
  change Tree.branch (118 : Fin 173) _ = Tree.branch (118 : Fin 173) _
  apply congrArg (Tree.branch (118 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0069
  · rfl
  · rfl
  · rfl

def B0067 : Block := .branch 128 ![576460752303423873, 216172782113785346, 18482772870728521732, 174224571863599779484201404844859254136840, 11874700803994150944246816192746548749567988432912, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), B0068, (.leaf 4 (Common.fact 294).pointIds 294), (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 296).pointIds 296)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M7500_7700.SplitData.node0067 := by
  change Tree.branch (128 : Fin 173) _ = Tree.branch (128 : Fin 173) _
  apply congrArg (Tree.branch (128 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0068
  · rfl
  · rfl
  · rfl

def B0066 : Block := .branch 137 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 11874700803994150944246816192746548749567988432912, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 286).pointIds 286), (.leaf 1 (Common.fact 287).pointIds 287), (.leaf 2 (Common.fact 288).pointIds 288), B0067, (.leaf 4 (Common.fact 289).pointIds 289), (.leaf 5 (Common.fact 290).pointIds 290), (.leaf 0 [] 0)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M7500_7700.SplitData.node0066 := by
  change Tree.branch (137 : Fin 173) _ = Tree.branch (137 : Fin 173) _
  apply congrArg (Tree.branch (137 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0067
  · rfl
  · rfl
  · rfl

def B0065 : Block := .branch 163 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 182687705346927598617337531016284592320528089104, 93536104789177786765035829293842113257979683143712, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 280).pointIds 280), (.leaf 1 (Common.fact 281).pointIds 281), (.leaf 2 (Common.fact 282).pointIds 282), (.leaf 3 (Common.fact 283).pointIds 283), B0066, (.leaf 5 (Common.fact 284).pointIds 284), (.leaf 6 (Common.fact 285).pointIds 285)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M7500_7700.SplitData.node0065 := by
  change Tree.branch (163 : Fin 173) _ = Tree.branch (163 : Fin 173) _
  apply congrArg (Tree.branch (163 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0066
  · rfl
  · rfl

def B0064 : Block := .branch 166 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 182687705346927598617337531016284592320528089104, 393248, 2854517190078347528661013270175091562489839680] ![(.leaf 0 (Common.fact 278).pointIds 278), (.leaf 1 (Common.fact 207).pointIds 207), (.leaf 2 (Common.fact 208).pointIds 208), (.leaf 3 (Common.fact 209).pointIds 209), (.leaf 4 (Common.fact 210).pointIds 210), B0065, (.leaf 6 (Common.fact 279).pointIds 279)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M7500_7700.SplitData.node0064 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · rfl

def B0063 : Block := .branch 151 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 182688055157200793342077971365381032178249465872, 42535295865117307932921825928971419680, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), (.leaf 3 (Common.fact 275).pointIds 275), (.leaf 4 (Common.fact 276).pointIds 276), (.leaf 5 (Common.fact 277).pointIds 277), B0064]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M7500_7700.SplitData.node0063 := by
  change Tree.branch (151 : Fin 173) _ = Tree.branch (151 : Fin 173) _
  apply congrArg (Tree.branch (151 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0064

def B0062 : Block := .branch 157 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 350490837928566617367275845654721257898000, 42535295865117307932921825928971419680, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 188).pointIds 188), (.leaf 1 (Common.fact 189).pointIds 189), (.leaf 2 (Common.fact 190).pointIds 190), (.leaf 3 (Common.fact 191).pointIds 191), B0063, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 0 [] 0)]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M7500_7700.SplitData.node0062 := by
  change Tree.branch (157 : Fin 173) _ = Tree.branch (157 : Fin 173) _
  apply congrArg (Tree.branch (157 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0063
  · rfl
  · rfl

def B0061 : Block := .branch 125 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 350490837928566617367275845654721257898000, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 265).pointIds 265), (.leaf 1 (Common.fact 266).pointIds 266), (.leaf 2 (Common.fact 267).pointIds 267), (.leaf 3 (Common.fact 268).pointIds 268), (.leaf 4 (Common.fact 269).pointIds 269), B0062, (.leaf 6 (Common.fact 270).pointIds 270)]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M7500_7700.SplitData.node0061 := by
  change Tree.branch (125 : Fin 173) _ = Tree.branch (125 : Fin 173) _
  apply congrArg (Tree.branch (125 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0062
  · rfl

def B0060 : Block := .branch 129 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 349810273194724740440349096439857721475088, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 259).pointIds 259), (.leaf 1 (Common.fact 260).pointIds 260), (.leaf 2 (Common.fact 261).pointIds 261), (.leaf 3 (Common.fact 262).pointIds 262), B0061, (.leaf 5 (Common.fact 263).pointIds 263), (.leaf 6 (Common.fact 264).pointIds 264)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M7500_7700.SplitData.node0060 := by
  change Tree.branch (129 : Fin 173) _ = Tree.branch (129 : Fin 173) _
  apply congrArg (Tree.branch (129 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0061
  · rfl
  · rfl

def B0059 : Block := .branch 142 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 349810273194724740440349096439857721475088, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 148).pointIds 148), (.leaf 1 (Common.fact 149).pointIds 149), (.leaf 2 (Common.fact 150).pointIds 150), (.leaf 3 (Common.fact 151).pointIds 151), (.leaf 4 (Common.fact 258).pointIds 258), (.leaf 5 (Common.fact 152).pointIds 152), B0060]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M7500_7700.SplitData.node0059 := by
  change Tree.branch (142 : Fin 173) _ = Tree.branch (142 : Fin 173) _
  apply congrArg (Tree.branch (142 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0060

def B0058 : Block := .branch 130 ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804666427766544441331276101289724346432] ![(.leaf 0 (Common.fact 252).pointIds 252), (.leaf 1 (Common.fact 253).pointIds 253), (.leaf 2 (Common.fact 254).pointIds 254), (.leaf 3 (Common.fact 255).pointIds 255), B0059, (.leaf 5 (Common.fact 256).pointIds 256), (.leaf 6 (Common.fact 257).pointIds 257)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M7500_7700.SplitData.node0058 := by
  change Tree.branch (130 : Fin 173) _ = Tree.branch (130 : Fin 173) _
  apply congrArg (Tree.branch (130 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl

theorem accepted0058 : B0058.accepted = true := by decide +kernel
theorem checked0058 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0058 (maskNeeds ![576460752303423873, 216172782113785346, 18482772870728521732, 79286190953605839793929871368, 348449143727040986586495598010130648629264, 393248, 21804666427766544441331276101289724346432]) := by
  rw [← treeEq0058]
  exact B0058.sound accepted0058
#print axioms checked0058

def B0157 : Block := .branch 171 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 509).pointIds 509), (.leaf 1 (Common.fact 510).pointIds 510), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 512).pointIds 512), (.leaf 4 (Common.fact 513).pointIds 513), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M7500_7700.SplitData.node0157 := by
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
  · rfl

def B0156 : Block := .branch 170 ![94266855607843243416434530245027883298303978242433, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 503).pointIds 503), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), B0157, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M7500_7700.SplitData.node0156 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0157
  · rfl

def B0159 : Block := .branch 171 ![467680523945888939018743655604266424221891446178177, 2192252455996354377305527249074424529483898816002, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 518).pointIds 518), (.leaf 1 (Common.fact 519).pointIds 519), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 512).pointIds 512), (.leaf 4 (Common.fact 513).pointIds 513), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0159 : B0159.tree = HexagonCover.NBand.M7500_7700.SplitData.node0159 := by
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
  · rfl

def B0158 : Block := .branch 170 ![467680523945888939018743655604266424221891446178177, 2192252455996354377305527249074424529483898816002, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 516).pointIds 516), (.leaf 1 (Common.fact 517).pointIds 517), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), B0159, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M7500_7700.SplitData.node0158 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0159
  · rfl

def B0161 : Block := .branch 171 ![467680523945888939018743655604266424221891446178177, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 1496577676626844588240573268701473812127674924400672, 733605335850202510053956181491265657225401073728] ![(.leaf 0 (Common.fact 518).pointIds 518), (.leaf 1 (Common.fact 510).pointIds 510), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 512).pointIds 512), (.leaf 4 (Common.fact 513).pointIds 513), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 521).pointIds 521)]
theorem treeEq0161 : B0161.tree = HexagonCover.NBand.M7500_7700.SplitData.node0161 := by
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
  · rfl

def B0160 : Block := .branch 170 ![467680523945888939018743655604266424221891446178177, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 733605335850202510053956181491265657225401073728] ![(.leaf 0 (Common.fact 516).pointIds 516), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 507).pointIds 507), B0161, (.leaf 6 (Common.fact 520).pointIds 520)]
theorem treeEq0160 : B0160.tree = HexagonCover.NBand.M7500_7700.SplitData.node0160 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0161
  · rfl

def B0155 : Block := .branch 159 ![467680523945888939018743655604266424221891446178177, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 2854517184751050952113765133124147397434802240] ![B0156, B0158, (.leaf 2 (Common.fact 499).pointIds 499), (.leaf 3 (Common.fact 500).pointIds 500), (.leaf 4 (Common.fact 501).pointIds 501), (.leaf 5 (Common.fact 502).pointIds 502), B0160]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M7500_7700.SplitData.node0155 := by
  change Tree.branch (159 : Fin 173) _ = Tree.branch (159 : Fin 173) _
  apply congrArg (Tree.branch (159 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0156
  · exact treeEq0158
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0160

def B0162 : Block := .branch 171 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177786765035829293842113257979683143712, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 522).pointIds 522), (.leaf 1 (Common.fact 510).pointIds 510), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 512).pointIds 512), (.leaf 4 (Common.fact 513).pointIds 513), (.leaf 5 (Common.fact 523).pointIds 523), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0162 : B0162.tree = HexagonCover.NBand.M7500_7700.SplitData.node0162 := by
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
  · rfl

def B0154 : Block := .branch 166 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 393248, 2854517184751050952113765133124147397434802240] ![B0155, (.leaf 1 (Common.fact 207).pointIds 207), (.leaf 2 (Common.fact 208).pointIds 208), (.leaf 3 (Common.fact 209).pointIds 209), (.leaf 4 (Common.fact 210).pointIds 210), B0162, (.leaf 6 (Common.fact 498).pointIds 498)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M7500_7700.SplitData.node0154 := by
  change Tree.branch (166 : Fin 173) _ = Tree.branch (166 : Fin 173) _
  apply congrArg (Tree.branch (166 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0155
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0162
  · rfl

def B0163 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 46768052394631428678383031954853978454918812794912, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 524).pointIds 524), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 506).pointIds 506), (.leaf 4 (Common.fact 525).pointIds 525), (.leaf 5 (Common.fact 526).pointIds 526), (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0163 : B0163.tree = HexagonCover.NBand.M7500_7700.SplitData.node0163 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0153 : Block := .branch 165 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 377).pointIds 377), (.leaf 1 (Common.fact 378).pointIds 378), (.leaf 2 (Common.fact 379).pointIds 379), (.leaf 3 (Common.fact 380).pointIds 380), B0154, B0163, (.leaf 0 [] 0)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M7500_7700.SplitData.node0153 := by
  change Tree.branch (165 : Fin 173) _ = Tree.branch (165 : Fin 173) _
  apply congrArg (Tree.branch (165 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0154
  · exact treeEq0163
  · rfl

def B0165 : Block := .branch 171 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 522).pointIds 522), (.leaf 1 (Common.fact 510).pointIds 510), (.leaf 2 (Common.fact 511).pointIds 511), (.leaf 3 (Common.fact 529).pointIds 529), (.leaf 4 (Common.fact 530).pointIds 530), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0165 : B0165.tree = HexagonCover.NBand.M7500_7700.SplitData.node0165 := by
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
  · rfl

def B0164 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 524).pointIds 524), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 505).pointIds 505), (.leaf 3 (Common.fact 527).pointIds 527), (.leaf 4 (Common.fact 528).pointIds 528), B0165, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0164 : B0164.tree = HexagonCover.NBand.M7500_7700.SplitData.node0164 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0165
  · rfl

def B0152 : Block := .branch 162 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 372).pointIds 372), (.leaf 1 (Common.fact 373).pointIds 373), (.leaf 2 (Common.fact 374).pointIds 374), B0153, B0164, (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 497).pointIds 497)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M7500_7700.SplitData.node0152 := by
  change Tree.branch (162 : Fin 173) _ = Tree.branch (162 : Fin 173) _
  apply congrArg (Tree.branch (162 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0153
  · exact treeEq0164
  · rfl
  · rfl

def B0167 : Block := .branch 171 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 1496577676626844588240573268701473812127674924400672, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 522).pointIds 522), (.leaf 1 (Common.fact 510).pointIds 510), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 534).pointIds 534), (.leaf 4 (Common.fact 535).pointIds 535), (.leaf 5 (Common.fact 514).pointIds 514), (.leaf 6 (Common.fact 515).pointIds 515)]
theorem treeEq0167 : B0167.tree = HexagonCover.NBand.M7500_7700.SplitData.node0167 := by
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
  · rfl

def B0166 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 393248, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 524).pointIds 524), (.leaf 1 (Common.fact 504).pointIds 504), (.leaf 2 (Common.fact 531).pointIds 531), (.leaf 3 (Common.fact 532).pointIds 532), (.leaf 4 (Common.fact 525).pointIds 525), B0167, (.leaf 6 (Common.fact 508).pointIds 508)]
theorem treeEq0166 : B0166.tree = HexagonCover.NBand.M7500_7700.SplitData.node0166 := by
  change Tree.branch (170 : Fin 173) _ = Tree.branch (170 : Fin 173) _
  apply congrArg (Tree.branch (170 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0167
  · rfl

def B0151 : Block := .branch 161 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), B0152, B0166, (.leaf 4 (Common.fact 369).pointIds 369), (.leaf 5 (Common.fact 370).pointIds 370), (.leaf 6 (Common.fact 496).pointIds 496)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M7500_7700.SplitData.node0151 := by
  change Tree.branch (161 : Fin 173) _ = Tree.branch (161 : Fin 173) _
  apply congrArg (Tree.branch (161 : Fin 173))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0152
  · exact treeEq0166
  · rfl
  · rfl
  · rfl

def B0150 : Block := .branch 168 ![5193564509135055857931993032425857, 1461501637330902918204303802735925709793382106626, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0151, (.leaf 1 (Common.fact 490).pointIds 490), (.leaf 2 (Common.fact 491).pointIds 491), (.leaf 3 (Common.fact 492).pointIds 492), (.leaf 4 (Common.fact 493).pointIds 493), (.leaf 5 (Common.fact 494).pointIds 494), (.leaf 6 (Common.fact 495).pointIds 495)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M7500_7700.SplitData.node0150 := by
  change Tree.branch (168 : Fin 173) _ = Tree.branch (168 : Fin 173) _
  apply congrArg (Tree.branch (168 : Fin 173))
  funext i
  fin_cases i
  · exact treeEq0151
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem accepted0150 : B0150.accepted = true := by decide +kernel
theorem checked0150 : CheckedWith (fun (_ : Fin 173) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7500_7700.SplitData.node0150 (maskNeeds ![5193564509135055857931993032425857, 1461501637330902918204303802735925709793382106626, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536]) := by
  rw [← treeEq0150]
  exact B0150.sound accepted0150
#print axioms checked0150

end HexagonCover.NBand.M7500_7700.SplitTree.Run0000
