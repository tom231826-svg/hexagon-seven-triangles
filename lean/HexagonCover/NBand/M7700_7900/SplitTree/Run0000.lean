import HexagonCover.NBand.M7700_7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.NBand.M7700_7900.SplitTree.Run0000
open OwnerTree HexagonCover.NBand.M7700_7900

abbrev Block := Chunk (n := 172) (Certificate := Fin 836) (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck

def B0082 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 386).pointIds 386), (.leaf 3 (Common.fact 387).pointIds 387), (.leaf 4 (Common.fact 388).pointIds 388), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0082 : B0082.tree = HexagonCover.NBand.M7700_7900.SplitData.node0082 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0083 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 386).pointIds 386), (.leaf 3 (Common.fact 387).pointIds 387), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 392).pointIds 392), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0083 : B0083.tree = HexagonCover.NBand.M7700_7900.SplitData.node0083 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0081 : Block := .branch 165 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), B0082, B0083, (.leaf 0 [] 0)]
theorem treeEq0081 : B0081.tree = HexagonCover.NBand.M7700_7900.SplitData.node0081 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0082
  · exact treeEq0083
  · rfl

def B0084 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 386).pointIds 386), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 394).pointIds 394), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0084 : B0084.tree = HexagonCover.NBand.M7700_7900.SplitData.node0084 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 162 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163493792686350461813408661962218799168] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0081, B0084, (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 379).pointIds 379)]
theorem treeEq0080 : B0080.tree = HexagonCover.NBand.M7700_7900.SplitData.node0080 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0081
  · exact treeEq0084
  · rfl
  · rfl

def B0085 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 395).pointIds 395), (.leaf 3 (Common.fact 396).pointIds 396), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0085 : B0085.tree = HexagonCover.NBand.M7700_7900.SplitData.node0085 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0079 : Block := .branch 161 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), B0080, B0085, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 374).pointIds 374)]
theorem treeEq0079 : B0079.tree = HexagonCover.NBand.M7700_7900.SplitData.node0079 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0080
  · exact treeEq0085
  · rfl
  · rfl
  · rfl

def B0090 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0090 : B0090.tree = HexagonCover.NBand.M7700_7900.SplitData.node0090 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 405).pointIds 405), (.leaf 5 (Common.fact 406).pointIds 406), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0091 : B0091.tree = HexagonCover.NBand.M7700_7900.SplitData.node0091 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0089 : Block := .branch 165 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), B0090, B0091, (.leaf 0 [] 0)]
theorem treeEq0089 : B0089.tree = HexagonCover.NBand.M7700_7900.SplitData.node0089 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0090
  · exact treeEq0091
  · rfl

def B0092 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), (.leaf 2 (Common.fact 400).pointIds 400), (.leaf 3 (Common.fact 407).pointIds 407), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0092 : B0092.tree = HexagonCover.NBand.M7700_7900.SplitData.node0092 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0088 : Block := .branch 162 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163493792686350461813408661962218799168] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0089, B0092, (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 379).pointIds 379)]
theorem treeEq0088 : B0088.tree = HexagonCover.NBand.M7700_7900.SplitData.node0088 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0089
  · exact treeEq0092
  · rfl
  · rfl

def B0093 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 399).pointIds 399), (.leaf 2 (Common.fact 409).pointIds 409), (.leaf 3 (Common.fact 410).pointIds 410), (.leaf 4 (Common.fact 405).pointIds 405), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0093 : B0093.tree = HexagonCover.NBand.M7700_7900.SplitData.node0093 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0087 : Block := .branch 161 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), B0088, B0093, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 374).pointIds 374)]
theorem treeEq0087 : B0087.tree = HexagonCover.NBand.M7700_7900.SplitData.node0087 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0088
  · exact treeEq0093
  · rfl
  · rfl
  · rfl

def B0086 : Block := .branch 168 ![604463486268066890776961, 151115727451828646839810, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 384).pointIds 384), B0087, (.leaf 2 (Common.fact 397).pointIds 397), (.leaf 3 (Common.fact 393).pointIds 393), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0086 : B0086.tree = HexagonCover.NBand.M7700_7900.SplitData.node0086 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0087
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0078 : Block := .branch 160 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 365).pointIds 365), B0079, B0086, (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 369).pointIds 369)]
theorem treeEq0078 : B0078.tree = HexagonCover.NBand.M7700_7900.SplitData.node0078 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0079
  · exact treeEq0086
  · rfl
  · rfl
  · rfl
  · rfl

def B0094 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 411).pointIds 411), (.leaf 2 (Common.fact 412).pointIds 412), (.leaf 3 (Common.fact 413).pointIds 413), (.leaf 4 (Common.fact 405).pointIds 405), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 414).pointIds 414)]
theorem treeEq0094 : B0094.tree = HexagonCover.NBand.M7700_7900.SplitData.node0094 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0077 : Block := .branch 86 ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 360).pointIds 360), (.leaf 1 (Common.fact 361).pointIds 361), (.leaf 2 (Common.fact 362).pointIds 362), B0078, (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 364).pointIds 364), B0094]
theorem treeEq0077 : B0077.tree = HexagonCover.NBand.M7700_7900.SplitData.node0077 := by
  change Tree.branch (86 : Fin 172) _ = Tree.branch (86 : Fin 172) _
  apply congrArg (Tree.branch (86 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0078
  · rfl
  · rfl
  · exact treeEq0094

theorem accepted0077 : B0077.accepted = true := by decide +kernel
theorem checked0077 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0077 (maskNeeds ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760]) := by
  rw [← treeEq0077]
  exact B0077.sound accepted0077
#print axioms checked0077

def Tip0072_0077 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0077 ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] checked0077
def B0097 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 417).pointIds 417), (.leaf 3 (Common.fact 396).pointIds 396), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0097 : B0097.tree = HexagonCover.NBand.M7700_7900.SplitData.node0097 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0096 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 365).pointIds 365), B0097, (.leaf 2 (Common.fact 416).pointIds 416), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 369).pointIds 369)]
theorem treeEq0096 : B0096.tree = HexagonCover.NBand.M7700_7900.SplitData.node0096 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0097
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0095 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 415).pointIds 415), B0096, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 374).pointIds 374)]
theorem treeEq0095 : B0095.tree = HexagonCover.NBand.M7700_7900.SplitData.node0095 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0096
  · rfl
  · rfl
  · rfl

def B0076 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 355).pointIds 355), Tip0072_0077, B0095, (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0076 : B0076.tree = HexagonCover.NBand.M7700_7900.SplitData.node0076 := by
  change Tree.branch (77 : Fin 172) _ = Tree.branch (77 : Fin 172) _
  apply congrArg (Tree.branch (77 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0095
  · rfl
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 398).pointIds 398), (.leaf 1 (Common.fact 411).pointIds 411), (.leaf 2 (Common.fact 421).pointIds 421), (.leaf 3 (Common.fact 422).pointIds 422), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0101 : B0101.tree = HexagonCover.NBand.M7700_7900.SplitData.node0101 := by
  change Tree.branch (169 : Fin 172) _ = Tree.branch (169 : Fin 172) _
  apply congrArg (Tree.branch (169 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 355).pointIds 355), B0101, (.leaf 2 (Common.fact 420).pointIds 420), (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0100 : B0100.tree = HexagonCover.NBand.M7700_7900.SplitData.node0100 := by
  change Tree.branch (77 : Fin 172) _ = Tree.branch (77 : Fin 172) _
  apply congrArg (Tree.branch (77 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0099 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), B0100, (.leaf 3 (Common.fact 419).pointIds 419), (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 374).pointIds 374)]
theorem treeEq0099 : B0099.tree = HexagonCover.NBand.M7700_7900.SplitData.node0099 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0100
  · rfl
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 162 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), (.leaf 3 (Common.fact 418).pointIds 418), B0099, (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 379).pointIds 379)]
theorem treeEq0098 : B0098.tree = HexagonCover.NBand.M7700_7900.SplitData.node0098 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0099
  · rfl
  · rfl

def B0075 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156381292641396099778801565760] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0076, B0098, (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0075 : B0075.tree = HexagonCover.NBand.M7700_7900.SplitData.node0075 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0076
  · exact treeEq0098
  · rfl
  · rfl
  · rfl

def B0109 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 384).pointIds 384), (.leaf 1 (Common.fact 385).pointIds 385), (.leaf 2 (Common.fact 450).pointIds 450), (.leaf 3 (Common.fact 396).pointIds 396), (.leaf 4 (Common.fact 391).pointIds 391), (.leaf 5 (Common.fact 389).pointIds 389), (.leaf 6 (Common.fact 390).pointIds 390)]
theorem treeEq0109 : B0109.tree = HexagonCover.NBand.M7700_7900.SplitData.node0109 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0108 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 365).pointIds 365), B0109, (.leaf 2 (Common.fact 449).pointIds 449), (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 369).pointIds 369)]
theorem treeEq0108 : B0108.tree = HexagonCover.NBand.M7700_7900.SplitData.node0108 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0109
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0107 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 351).pointIds 351), (.leaf 1 (Common.fact 352).pointIds 352), B0108, (.leaf 3 (Common.fact 448).pointIds 448), (.leaf 4 (Common.fact 353).pointIds 353), (.leaf 5 (Common.fact 354).pointIds 354), (.leaf 0 [] 0)]
theorem treeEq0107 : B0107.tree = HexagonCover.NBand.M7700_7900.SplitData.node0107 := by
  change Tree.branch (71 : Fin 172) _ = Tree.branch (71 : Fin 172) _
  apply congrArg (Tree.branch (71 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0108
  · rfl
  · rfl
  · rfl
  · rfl

def B0106 : Block := .branch 72 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 442).pointIds 442), (.leaf 1 (Common.fact 443).pointIds 443), B0107, (.leaf 3 (Common.fact 444).pointIds 444), (.leaf 4 (Common.fact 445).pointIds 445), (.leaf 5 (Common.fact 446).pointIds 446), (.leaf 6 (Common.fact 447).pointIds 447)]
theorem treeEq0106 : B0106.tree = HexagonCover.NBand.M7700_7900.SplitData.node0106 := by
  change Tree.branch (72 : Fin 172) _ = Tree.branch (72 : Fin 172) _
  apply congrArg (Tree.branch (72 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0107
  · rfl
  · rfl
  · rfl
  · rfl

def B0105 : Block := .branch 73 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 436).pointIds 436), (.leaf 1 (Common.fact 437).pointIds 437), B0106, (.leaf 3 (Common.fact 438).pointIds 438), (.leaf 4 (Common.fact 439).pointIds 439), (.leaf 5 (Common.fact 440).pointIds 440), (.leaf 6 (Common.fact 441).pointIds 441)]
theorem treeEq0105 : B0105.tree = HexagonCover.NBand.M7700_7900.SplitData.node0105 := by
  change Tree.branch (73 : Fin 172) _ = Tree.branch (73 : Fin 172) _
  apply congrArg (Tree.branch (73 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0106
  · rfl
  · rfl
  · rfl
  · rfl

def B0104 : Block := .branch 74 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528052529534156071807631574754710076784704] ![(.leaf 0 (Common.fact 430).pointIds 430), (.leaf 1 (Common.fact 431).pointIds 431), B0105, (.leaf 3 (Common.fact 432).pointIds 432), (.leaf 4 (Common.fact 433).pointIds 433), (.leaf 5 (Common.fact 434).pointIds 434), (.leaf 6 (Common.fact 435).pointIds 435)]
theorem treeEq0104 : B0104.tree = HexagonCover.NBand.M7700_7900.SplitData.node0104 := by
  change Tree.branch (74 : Fin 172) _ = Tree.branch (74 : Fin 172) _
  apply congrArg (Tree.branch (74 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0105
  · rfl
  · rfl
  · rfl
  · rfl

def B0103 : Block := .branch 75 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797182088630461598035667674562297920] ![(.leaf 0 (Common.fact 424).pointIds 424), (.leaf 1 (Common.fact 425).pointIds 425), B0104, (.leaf 3 (Common.fact 426).pointIds 426), (.leaf 4 (Common.fact 427).pointIds 427), (.leaf 5 (Common.fact 428).pointIds 428), (.leaf 6 (Common.fact 429).pointIds 429)]
theorem treeEq0103 : B0103.tree = HexagonCover.NBand.M7700_7900.SplitData.node0103 := by
  change Tree.branch (75 : Fin 172) _ = Tree.branch (75 : Fin 172) _
  apply congrArg (Tree.branch (75 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0104
  · rfl
  · rfl
  · rfl
  · rfl

def B0102 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797182088630461598035667674562297920] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), (.leaf 2 (Common.fact 423).pointIds 423), B0103, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 374).pointIds 374)]
theorem treeEq0102 : B0102.tree = HexagonCover.NBand.M7700_7900.SplitData.node0102 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0103
  · rfl
  · rfl
  · rfl

def B0074 : Block := .branch 66 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797182088939946607857012743287078976] ![(.leaf 0 (Common.fact 346).pointIds 346), B0075, B0102, (.leaf 3 (Common.fact 347).pointIds 347), (.leaf 4 (Common.fact 348).pointIds 348), (.leaf 5 (Common.fact 349).pointIds 349), (.leaf 6 (Common.fact 350).pointIds 350)]
theorem treeEq0074 : B0074.tree = HexagonCover.NBand.M7700_7900.SplitData.node0074 := by
  change Tree.branch (66 : Fin 172) _ = Tree.branch (66 : Fin 172) _
  apply congrArg (Tree.branch (66 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0075
  · exact treeEq0102
  · rfl
  · rfl
  · rfl
  · rfl

def B0073 : Block := .branch 91 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797182086464066529286252193488830528] ![(.leaf 0 (Common.fact 340).pointIds 340), (.leaf 1 (Common.fact 341).pointIds 341), (.leaf 2 (Common.fact 342).pointIds 342), (.leaf 3 (Common.fact 343).pointIds 343), (.leaf 4 (Common.fact 344).pointIds 344), (.leaf 5 (Common.fact 345).pointIds 345), B0074]
theorem treeEq0073 : B0073.tree = HexagonCover.NBand.M7700_7900.SplitData.node0073 := by
  change Tree.branch (91 : Fin 172) _ = Tree.branch (91 : Fin 172) _
  apply congrArg (Tree.branch (91 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0074

def B0072 : Block := .branch 102 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015861665616368646206676009024] ![(.leaf 0 (Common.fact 334).pointIds 334), (.leaf 1 (Common.fact 335).pointIds 335), (.leaf 2 (Common.fact 336).pointIds 336), (.leaf 3 (Common.fact 337).pointIds 337), (.leaf 4 (Common.fact 338).pointIds 338), (.leaf 5 (Common.fact 339).pointIds 339), B0073]
theorem treeEq0072 : B0072.tree = HexagonCover.NBand.M7700_7900.SplitData.node0072 := by
  change Tree.branch (102 : Fin 172) _ = Tree.branch (102 : Fin 172) _
  apply congrArg (Tree.branch (102 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0073

theorem accepted0072 : B0072.accepted = true := by decide +kernel
theorem checked0072 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0072 (maskNeeds ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015861665616368646206676009024]) := by
  rw [← treeEq0072]
  exact B0072.sound accepted0072
#print axioms checked0072

def Tip0052_0072 : Block := .tip HexagonCover.NBand.M7700_7900.SplitData.node0072 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015861665616368646206676009024] checked0072
def B0071 : Block := .branch 87 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 328).pointIds 328), (.leaf 1 (Common.fact 329).pointIds 329), (.leaf 2 (Common.fact 330).pointIds 330), (.leaf 3 (Common.fact 331).pointIds 331), (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), Tip0052_0072]
theorem treeEq0071 : B0071.tree = HexagonCover.NBand.M7700_7900.SplitData.node0071 := by
  change Tree.branch (87 : Fin 172) _ = Tree.branch (87 : Fin 172) _
  apply congrArg (Tree.branch (87 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0070 : Block := .branch 76 ![604463486268066890776961, 302231526961251331606018, 9259400833873745924, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 322).pointIds 322), (.leaf 1 (Common.fact 323).pointIds 323), B0071, (.leaf 3 (Common.fact 324).pointIds 324), (.leaf 4 (Common.fact 325).pointIds 325), (.leaf 5 (Common.fact 326).pointIds 326), (.leaf 6 (Common.fact 327).pointIds 327)]
theorem treeEq0070 : B0070.tree = HexagonCover.NBand.M7700_7900.SplitData.node0070 := by
  change Tree.branch (76 : Fin 172) _ = Tree.branch (76 : Fin 172) _
  apply congrArg (Tree.branch (76 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0071
  · rfl
  · rfl
  · rfl
  · rfl

def B0069 : Block := .branch 97 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863520531978874026673198914887688, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 316).pointIds 316), (.leaf 1 (Common.fact 317).pointIds 317), (.leaf 2 (Common.fact 318).pointIds 318), B0070, (.leaf 4 (Common.fact 319).pointIds 319), (.leaf 5 (Common.fact 320).pointIds 320), (.leaf 6 (Common.fact 321).pointIds 321)]
theorem treeEq0069 : B0069.tree = HexagonCover.NBand.M7700_7900.SplitData.node0069 := by
  change Tree.branch (97 : Fin 172) _ = Tree.branch (97 : Fin 172) _
  apply congrArg (Tree.branch (97 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0070
  · rfl
  · rfl
  · rfl

def B0068 : Block := .branch 107 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863520531978874026673198914887688, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 310).pointIds 310), (.leaf 1 (Common.fact 311).pointIds 311), (.leaf 2 (Common.fact 312).pointIds 312), B0069, (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), (.leaf 6 (Common.fact 315).pointIds 315)]
theorem treeEq0068 : B0068.tree = HexagonCover.NBand.M7700_7900.SplitData.node0068 := by
  change Tree.branch (107 : Fin 172) _ = Tree.branch (107 : Fin 172) _
  apply congrArg (Tree.branch (107 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0069
  · rfl
  · rfl
  · rfl

def B0067 : Block := .branch 118 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863520531978874026673198914887688, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 304).pointIds 304), (.leaf 1 (Common.fact 305).pointIds 305), (.leaf 2 (Common.fact 306).pointIds 306), B0068, (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), (.leaf 6 (Common.fact 309).pointIds 309)]
theorem treeEq0067 : B0067.tree = HexagonCover.NBand.M7700_7900.SplitData.node0067 := by
  change Tree.branch (118 : Fin 172) _ = Tree.branch (118 : Fin 172) _
  apply congrArg (Tree.branch (118 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0068
  · rfl
  · rfl
  · rfl

def B0066 : Block := .branch 128 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863520531978874026673198914887688, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 298).pointIds 298), (.leaf 1 (Common.fact 299).pointIds 299), (.leaf 2 (Common.fact 300).pointIds 300), B0067, (.leaf 4 (Common.fact 301).pointIds 301), (.leaf 5 (Common.fact 302).pointIds 302), (.leaf 6 (Common.fact 303).pointIds 303)]
theorem treeEq0066 : B0066.tree = HexagonCover.NBand.M7700_7900.SplitData.node0066 := by
  change Tree.branch (128 : Fin 172) _ = Tree.branch (128 : Fin 172) _
  apply congrArg (Tree.branch (128 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0067
  · rfl
  · rfl
  · rfl

def B0065 : Block := .branch 137 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 38685626227668133590622216, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 293).pointIds 293), (.leaf 1 (Common.fact 294).pointIds 294), (.leaf 2 (Common.fact 295).pointIds 295), B0066, (.leaf 4 (Common.fact 296).pointIds 296), (.leaf 5 (Common.fact 297).pointIds 297), (.leaf 0 [] 0)]
theorem treeEq0065 : B0065.tree = HexagonCover.NBand.M7700_7900.SplitData.node0065 := by
  change Tree.branch (137 : Fin 172) _ = Tree.branch (137 : Fin 172) _
  apply congrArg (Tree.branch (137 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0066
  · rfl
  · rfl
  · rfl

def B0064 : Block := .branch 163 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 38685626227668133590622216, 182687704666363189294014262516262160613012242448, 93536104789177807534223263433152627379965000024096, 2854528073797177015706923111457973672313618496] ![(.leaf 0 (Common.fact 287).pointIds 287), (.leaf 1 (Common.fact 288).pointIds 288), (.leaf 2 (Common.fact 289).pointIds 289), (.leaf 3 (Common.fact 290).pointIds 290), B0065, (.leaf 5 (Common.fact 291).pointIds 291), (.leaf 6 (Common.fact 292).pointIds 292)]
theorem treeEq0064 : B0064.tree = HexagonCover.NBand.M7700_7900.SplitData.node0064 := by
  change Tree.branch (163 : Fin 172) _ = Tree.branch (163 : Fin 172) _
  apply congrArg (Tree.branch (163 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065
  · rfl
  · rfl

def B0063 : Block := .branch 88 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 38685626227668133590622216, 182687704666363189294014262516262160613012242448, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 76).pointIds 76), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 78).pointIds 78), (.leaf 3 (Common.fact 79).pointIds 79), (.leaf 4 (Common.fact 80).pointIds 80), (.leaf 5 (Common.fact 81).pointIds 81), B0064]
theorem treeEq0063 : B0063.tree = HexagonCover.NBand.M7700_7900.SplitData.node0063 := by
  change Tree.branch (88 : Fin 172) _ = Tree.branch (88 : Fin 172) _
  apply congrArg (Tree.branch (88 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0064

def B0062 : Block := .branch 78 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 38685626227668133590622216, 182687704666363189294014262516262160613012242448, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 100).pointIds 100), B0063, (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), (.leaf 4 (Common.fact 104).pointIds 104), (.leaf 5 (Common.fact 105).pointIds 105), (.leaf 6 (Common.fact 285).pointIds 285)]
theorem treeEq0062 : B0062.tree = HexagonCover.NBand.M7700_7900.SplitData.node0062 := by
  change Tree.branch (78 : Fin 172) _ = Tree.branch (78 : Fin 172) _
  apply congrArg (Tree.branch (78 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0063
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0061 : Block := .branch 108 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 279).pointIds 279), (.leaf 1 (Common.fact 280).pointIds 280), (.leaf 2 (Common.fact 281).pointIds 281), (.leaf 3 (Common.fact 282).pointIds 282), B0062, (.leaf 5 (Common.fact 283).pointIds 283), (.leaf 6 (Common.fact 284).pointIds 284)]
theorem treeEq0061 : B0061.tree = HexagonCover.NBand.M7700_7900.SplitData.node0061 := by
  change Tree.branch (108 : Fin 172) _ = Tree.branch (108 : Fin 172) _
  apply congrArg (Tree.branch (108 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0062
  · rfl
  · rfl

def B0060 : Block := .branch 119 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 38685626227668133590622216, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 273).pointIds 273), (.leaf 1 (Common.fact 274).pointIds 274), (.leaf 2 (Common.fact 275).pointIds 275), (.leaf 3 (Common.fact 276).pointIds 276), B0061, (.leaf 5 (Common.fact 277).pointIds 277), (.leaf 6 (Common.fact 278).pointIds 278)]
theorem treeEq0060 : B0060.tree = HexagonCover.NBand.M7700_7900.SplitData.node0060 := by
  change Tree.branch (119 : Fin 172) _ = Tree.branch (119 : Fin 172) _
  apply congrArg (Tree.branch (119 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0061
  · rfl
  · rfl

def B0059 : Block := .branch 120 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 267).pointIds 267), (.leaf 1 (Common.fact 268).pointIds 268), (.leaf 2 (Common.fact 269).pointIds 269), (.leaf 3 (Common.fact 270).pointIds 270), B0060, (.leaf 5 (Common.fact 271).pointIds 271), (.leaf 6 (Common.fact 272).pointIds 272)]
theorem treeEq0059 : B0059.tree = HexagonCover.NBand.M7700_7900.SplitData.node0059 := by
  change Tree.branch (120 : Fin 172) _ = Tree.branch (120 : Fin 172) _
  apply congrArg (Tree.branch (120 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0060
  · rfl
  · rfl

def B0058 : Block := .branch 129 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177807534223263433152627379965000024096, 2854528073797177015397438101636628603588837440] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0059, (.leaf 5 (Common.fact 123).pointIds 123), (.leaf 6 (Common.fact 266).pointIds 266)]
theorem treeEq0058 : B0058.tree = HexagonCover.NBand.M7700_7900.SplitData.node0058 := by
  change Tree.branch (129 : Fin 172) _ = Tree.branch (129 : Fin 172) _
  apply congrArg (Tree.branch (129 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl

def B0057 : Block := .branch 114 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 2865683890914313061983621374766671692633210944] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), (.leaf 2 (Common.fact 262).pointIds 262), (.leaf 3 (Common.fact 263).pointIds 263), (.leaf 4 (Common.fact 264).pointIds 264), B0058, (.leaf 6 (Common.fact 265).pointIds 265)]
theorem treeEq0057 : B0057.tree = HexagonCover.NBand.M7700_7900.SplitData.node0057 := by
  change Tree.branch (114 : Fin 172) _ = Tree.branch (114 : Fin 172) _
  apply congrArg (Tree.branch (114 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · rfl

def B0056 : Block := .branch 131 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 2865683890914313061983621374766671692633210944] ![(.leaf 0 (Common.fact 254).pointIds 254), (.leaf 1 (Common.fact 255).pointIds 255), (.leaf 2 (Common.fact 256).pointIds 256), (.leaf 3 (Common.fact 257).pointIds 257), B0057, (.leaf 5 (Common.fact 258).pointIds 258), (.leaf 6 (Common.fact 259).pointIds 259)]
theorem treeEq0056 : B0056.tree = HexagonCover.NBand.M7700_7900.SplitData.node0056 := by
  change Tree.branch (131 : Fin 172) _ = Tree.branch (131 : Fin 172) _
  apply congrArg (Tree.branch (131 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl

def B0055 : Block := .branch 141 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 2865683890914313061983621374766671692633210944] ![(.leaf 0 (Common.fact 248).pointIds 248), (.leaf 1 (Common.fact 249).pointIds 249), (.leaf 2 (Common.fact 250).pointIds 250), (.leaf 3 (Common.fact 251).pointIds 251), B0056, (.leaf 5 (Common.fact 252).pointIds 252), (.leaf 6 (Common.fact 253).pointIds 253)]
theorem treeEq0055 : B0055.tree = HexagonCover.NBand.M7700_7900.SplitData.node0055 := by
  change Tree.branch (141 : Fin 172) _ = Tree.branch (141 : Fin 172) _
  apply congrArg (Tree.branch (141 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0056
  · rfl
  · rfl

def B0054 : Block := .branch 150 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182687704666362864775460604089535377456991666192, 93536104789177786765035829293842113257979683143712, 2865683890914313061983621374766671692633210944] ![(.leaf 0 (Common.fact 106).pointIds 106), (.leaf 1 (Common.fact 107).pointIds 107), (.leaf 2 (Common.fact 108).pointIds 108), (.leaf 3 (Common.fact 109).pointIds 109), B0055, (.leaf 5 (Common.fact 110).pointIds 110), (.leaf 6 (Common.fact 247).pointIds 247)]
theorem treeEq0054 : B0054.tree = HexagonCover.NBand.M7700_7900.SplitData.node0054 := by
  change Tree.branch (150 : Fin 172) _ = Tree.branch (150 : Fin 172) _
  apply congrArg (Tree.branch (150 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0055
  · rfl
  · rfl

def B0053 : Block := .branch 151 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688054476636059500201044438631817314713042960, 93536104789177786765035829293842113257979683143712, 11188505502393299867049435867681419867717696] ![(.leaf 0 (Common.fact 241).pointIds 241), (.leaf 1 (Common.fact 242).pointIds 242), (.leaf 2 (Common.fact 243).pointIds 243), (.leaf 3 (Common.fact 244).pointIds 244), (.leaf 4 (Common.fact 245).pointIds 245), (.leaf 5 (Common.fact 246).pointIds 246), B0054]
theorem treeEq0053 : B0053.tree = HexagonCover.NBand.M7700_7900.SplitData.node0053 := by
  change Tree.branch (151 : Fin 172) _ = Tree.branch (151 : Fin 172) _
  apply congrArg (Tree.branch (151 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0054

def B0052 : Block := .branch 166 ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688054476636059500201044438631817314713042960, 393248, 11188505502393299867049435867681419867717696] ![(.leaf 0 (Common.fact 235).pointIds 235), (.leaf 1 (Common.fact 236).pointIds 236), (.leaf 2 (Common.fact 237).pointIds 237), (.leaf 3 (Common.fact 238).pointIds 238), (.leaf 4 (Common.fact 239).pointIds 239), B0053, (.leaf 6 (Common.fact 240).pointIds 240)]
theorem treeEq0052 : B0052.tree = HexagonCover.NBand.M7700_7900.SplitData.node0052 := by
  change Tree.branch (166 : Fin 172) _ = Tree.branch (166 : Fin 172) _
  apply congrArg (Tree.branch (166 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0053
  · rfl

theorem accepted0052 : B0052.accepted = true := by decide +kernel
theorem checked0052 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0052 (maskNeeds ![604463486268066890776961, 72057594037929474, 9277485601127405572, 79266848140492005727134572552, 182688054476636059500201044438631817314713042960, 393248, 11188505502393299867049435867681419867717696]) := by
  rw [← treeEq0052]
  exact B0052.sound accepted0052
#print axioms checked0052

def B0151 : Block := .branch 170 ![467680523945888939018743655604266424221891446178177, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 520).pointIds 520), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0151 : B0151.tree = HexagonCover.NBand.M7700_7900.SplitData.node0151 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0152 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 93536104789177786765035829293842113257979683143712, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 527).pointIds 527), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 524).pointIds 524), (.leaf 5 (Common.fact 528).pointIds 528), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0152 : B0152.tree = HexagonCover.NBand.M7700_7900.SplitData.node0152 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0150 : Block := .branch 166 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58460065493236117052665946967078047569393322393616, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![B0151, (.leaf 1 (Common.fact 236).pointIds 236), (.leaf 2 (Common.fact 237).pointIds 237), (.leaf 3 (Common.fact 238).pointIds 238), (.leaf 4 (Common.fact 239).pointIds 239), B0152, (.leaf 6 (Common.fact 519).pointIds 519)]
theorem treeEq0150 : B0150.tree = HexagonCover.NBand.M7700_7900.SplitData.node0150 := by
  change Tree.branch (166 : Fin 172) _ = Tree.branch (166 : Fin 172) _
  apply congrArg (Tree.branch (166 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0151
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0152
  · rfl

def B0153 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 46768052394631428678383031954853978454918812794912, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 527).pointIds 527), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 523).pointIds 523), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 530).pointIds 530), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0153 : B0153.tree = HexagonCover.NBand.M7700_7900.SplitData.node0153 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0149 : Block := .branch 165 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 380).pointIds 380), (.leaf 1 (Common.fact 381).pointIds 381), (.leaf 2 (Common.fact 382).pointIds 382), (.leaf 3 (Common.fact 383).pointIds 383), B0150, B0153, (.leaf 0 [] 0)]
theorem treeEq0149 : B0149.tree = HexagonCover.NBand.M7700_7900.SplitData.node0149 := by
  change Tree.branch (165 : Fin 172) _ = Tree.branch (165 : Fin 172) _
  apply congrArg (Tree.branch (165 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0150
  · exact treeEq0153
  · rfl

def B0154 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 527).pointIds 527), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 522).pointIds 522), (.leaf 3 (Common.fact 531).pointIds 531), (.leaf 4 (Common.fact 532).pointIds 532), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0154 : B0154.tree = HexagonCover.NBand.M7700_7900.SplitData.node0154 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0148 : Block := .branch 162 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 375).pointIds 375), (.leaf 1 (Common.fact 376).pointIds 376), (.leaf 2 (Common.fact 377).pointIds 377), B0149, B0154, (.leaf 5 (Common.fact 378).pointIds 378), (.leaf 6 (Common.fact 518).pointIds 518)]
theorem treeEq0148 : B0148.tree = HexagonCover.NBand.M7700_7900.SplitData.node0148 := by
  change Tree.branch (162 : Fin 172) _ = Tree.branch (162 : Fin 172) _
  apply congrArg (Tree.branch (162 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0149
  · exact treeEq0154
  · rfl
  · rfl

def B0155 : Block := .branch 170 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 527).pointIds 527), (.leaf 1 (Common.fact 521).pointIds 521), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 534).pointIds 534), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0155 : B0155.tree = HexagonCover.NBand.M7700_7900.SplitData.node0155 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0147 : Block := .branch 161 ![374144419156711152253707826310424310963911763427713, 1461501637330902918204303802735925709793382106626, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 370).pointIds 370), (.leaf 1 (Common.fact 371).pointIds 371), B0148, B0155, (.leaf 4 (Common.fact 372).pointIds 372), (.leaf 5 (Common.fact 373).pointIds 373), (.leaf 6 (Common.fact 517).pointIds 517)]
theorem treeEq0147 : B0147.tree = HexagonCover.NBand.M7700_7900.SplitData.node0147 := by
  change Tree.branch (161 : Fin 172) _ = Tree.branch (161 : Fin 172) _
  apply congrArg (Tree.branch (161 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0148
  · exact treeEq0155
  · rfl
  · rfl
  · rfl

def B0146 : Block := .branch 168 ![5193564509135055857931993032425857, 1461501637330902918204303802735925709793382106626, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0147, (.leaf 1 (Common.fact 511).pointIds 511), (.leaf 2 (Common.fact 512).pointIds 512), (.leaf 3 (Common.fact 513).pointIds 513), (.leaf 4 (Common.fact 514).pointIds 514), (.leaf 5 (Common.fact 515).pointIds 515), (.leaf 6 (Common.fact 516).pointIds 516)]
theorem treeEq0146 : B0146.tree = HexagonCover.NBand.M7700_7900.SplitData.node0146 := by
  change Tree.branch (168 : Fin 172) _ = Tree.branch (168 : Fin 172) _
  apply congrArg (Tree.branch (168 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0147
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0156 : Block := .branch 170 ![5193564509135055857931993032425857, 618970019642690137449563650, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952113765133124147397434802240] ![(.leaf 0 (Common.fact 535).pointIds 535), (.leaf 1 (Common.fact 536).pointIds 536), (.leaf 2 (Common.fact 537).pointIds 537), (.leaf 3 (Common.fact 531).pointIds 531), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 526).pointIds 526)]
theorem treeEq0156 : B0156.tree = HexagonCover.NBand.M7700_7900.SplitData.node0156 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0145 : Block := .branch 160 ![5193564509135055857931993032425857, 618970019642690137449563650, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 365).pointIds 365), B0146, B0156, (.leaf 3 (Common.fact 366).pointIds 366), (.leaf 4 (Common.fact 367).pointIds 367), (.leaf 5 (Common.fact 368).pointIds 368), (.leaf 6 (Common.fact 510).pointIds 510)]
theorem treeEq0145 : B0145.tree = HexagonCover.NBand.M7700_7900.SplitData.node0145 := by
  change Tree.branch (160 : Fin 172) _ = Tree.branch (160 : Fin 172) _
  apply congrArg (Tree.branch (160 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0146
  · exact treeEq0156
  · rfl
  · rfl
  · rfl
  · rfl

def B0157 : Block := .branch 170 ![5193564509135055857931993032425857, 453347182355485940516354, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184751050952423250142945492466159583296] ![(.leaf 0 (Common.fact 535).pointIds 535), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 531).pointIds 531), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 539).pointIds 539)]
theorem treeEq0157 : B0157.tree = HexagonCover.NBand.M7700_7900.SplitData.node0157 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0144 : Block := .branch 89 ![5193564509135055857931993032425857, 453347182355485940516354, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![(.leaf 0 (Common.fact 505).pointIds 505), B0145, (.leaf 2 (Common.fact 506).pointIds 506), (.leaf 3 (Common.fact 507).pointIds 507), (.leaf 4 (Common.fact 508).pointIds 508), (.leaf 5 (Common.fact 509).pointIds 509), B0157]
theorem treeEq0144 : B0144.tree = HexagonCover.NBand.M7700_7900.SplitData.node0144 := by
  change Tree.branch (89 : Fin 172) _ = Tree.branch (89 : Fin 172) _
  apply congrArg (Tree.branch (89 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0145
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0157

def B0158 : Block := .branch 170 ![1267650600228229401496703205761, 453347182355485940516354, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 42535295865117307932921825928971419680, 2854517184756243248972299960752677893764022336] ![(.leaf 0 (Common.fact 540).pointIds 540), (.leaf 1 (Common.fact 538).pointIds 538), (.leaf 2 (Common.fact 533).pointIds 533), (.leaf 3 (Common.fact 531).pointIds 531), (.leaf 4 (Common.fact 529).pointIds 529), (.leaf 5 (Common.fact 525).pointIds 525), (.leaf 6 (Common.fact 541).pointIds 541)]
theorem treeEq0158 : B0158.tree = HexagonCover.NBand.M7700_7900.SplitData.node0158 := by
  change Tree.branch (170 : Fin 172) _ = Tree.branch (170 : Fin 172) _
  apply congrArg (Tree.branch (170 : Fin 172))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0143 : Block := .branch 112 ![1267650600228229401496703205761, 453347182355485940516354, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536] ![B0144, (.leaf 1 (Common.fact 500).pointIds 500), (.leaf 2 (Common.fact 501).pointIds 501), (.leaf 3 (Common.fact 502).pointIds 502), (.leaf 4 (Common.fact 503).pointIds 503), (.leaf 5 (Common.fact 504).pointIds 504), B0158]
theorem treeEq0143 : B0143.tree = HexagonCover.NBand.M7700_7900.SplitData.node0143 := by
  change Tree.branch (112 : Fin 172) _ = Tree.branch (112 : Fin 172) _
  apply congrArg (Tree.branch (112 : Fin 172))
  funext i
  fin_cases i
  · exact treeEq0144
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0158

theorem accepted0143 : B0143.accepted = true := by decide +kernel
theorem checked0143 : CheckedWith (fun (_ : Fin 172) => true) Common.allowed Semantics.leafCheck
    HexagonCover.NBand.M7700_7900.SplitData.node0143 (maskNeeds ![1267650600228229401496703205761, 453347182355485940516354, 77937529740219874547716, 174224571863520609350126482009466096082952, 11874879209275174779908625209992707504752520429584, 42535295865117307932921825928971419680, 2854522629268921687129180547117866305726185536]) := by
  rw [← treeEq0143]
  exact B0143.sound accepted0143
#print axioms checked0143

end HexagonCover.NBand.M7700_7900.SplitTree.Run0000
