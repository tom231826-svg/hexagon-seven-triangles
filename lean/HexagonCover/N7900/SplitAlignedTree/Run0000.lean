import HexagonCover.N7900.SplitData
import HexagonCover.OwnerTreeChunk

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace HexagonCover.N7900.SplitAlignedTree.Run0000
open OwnerTree HexagonCover.N7900

abbrev Block := Chunk (n := 170) (Certificate := Fin 763) (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck

def B0074 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 355).pointIds 355), (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 357).pointIds 357), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0074 : B0074.tree = HexagonCover.N7900.SplitData.node0074 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0075 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 355).pointIds 355), (.leaf 3 (Common.fact 356).pointIds 356), (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 361).pointIds 361), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0075 : B0075.tree = HexagonCover.N7900.SplitData.node0075 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0073 : Block := .branch 165 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), B0074, B0075, (.leaf 0 [] 0)]
theorem treeEq0073 : B0073.tree = HexagonCover.N7900.SplitData.node0073 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0074
  · exact treeEq0075
  · rfl

def B0076 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 355).pointIds 355), (.leaf 3 (Common.fact 362).pointIds 362), (.leaf 4 (Common.fact 363).pointIds 363), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0076 : B0076.tree = HexagonCover.N7900.SplitData.node0076 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0072 : Block := .branch 162 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 2923003274661805836407369743351613006661011118084, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), B0073, B0076, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 348).pointIds 348)]
theorem treeEq0072 : B0072.tree = HexagonCover.N7900.SplitData.node0072 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0073
  · exact treeEq0076
  · rfl
  · rfl

def B0077 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 364).pointIds 364), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0077 : B0077.tree = HexagonCover.N7900.SplitData.node0077 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0071 : Block := .branch 161 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0072, B0077, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0071 : B0071.tree = HexagonCover.N7900.SplitData.node0071 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0072
  · exact treeEq0077
  · rfl
  · rfl
  · rfl

def B0082 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 58642753197902479917441407571167582946850313961488, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 369).pointIds 369), (.leaf 3 (Common.fact 370).pointIds 370), (.leaf 4 (Common.fact 371).pointIds 371), (.leaf 5 (Common.fact 372).pointIds 372), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0082 : B0082.tree = HexagonCover.N7900.SplitData.node0082 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0083 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 140304157183766700916741178080073684008954841399328, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 369).pointIds 369), (.leaf 3 (Common.fact 370).pointIds 370), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 375).pointIds 375), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0083 : B0083.tree = HexagonCover.N7900.SplitData.node0083 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0081 : Block := .branch 165 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 5846006723548183536335309995365386419956235657224, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), B0082, B0083, (.leaf 0 [] 0)]
theorem treeEq0081 : B0081.tree = HexagonCover.N7900.SplitData.node0081 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0082
  · exact treeEq0083
  · rfl

def B0084 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 369).pointIds 369), (.leaf 3 (Common.fact 376).pointIds 376), (.leaf 4 (Common.fact 377).pointIds 377), (.leaf 5 (Common.fact 372).pointIds 372), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0084 : B0084.tree = HexagonCover.N7900.SplitData.node0084 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0080 : Block := .branch 162 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 4384504911992708754611054500510032300402620241924, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629268926760207461538606232842337255488] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), B0081, B0084, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 348).pointIds 348)]
theorem treeEq0080 : B0080.tree = HexagonCover.N7900.SplitData.node0080 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0081
  · exact treeEq0084
  · rfl
  · rfl

def B0085 : Block := .branch 169 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 368).pointIds 368), (.leaf 2 (Common.fact 378).pointIds 378), (.leaf 3 (Common.fact 379).pointIds 379), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 372).pointIds 372), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0085 : B0085.tree = HexagonCover.N7900.SplitData.node0085 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0079 : Block := .branch 161 ![604463486268066890776961, 374144419156711147060143317326484180483747377841666, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0080, B0085, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0079 : B0079.tree = HexagonCover.N7900.SplitData.node0079 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0080
  · exact treeEq0085
  · rfl
  · rfl
  · rfl

def B0078 : Block := .branch 168 ![604463486268066890776961, 151115727451828646839810, 1461501637330902918203684835077466261090755155972, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 353).pointIds 353), B0079, (.leaf 2 (Common.fact 366).pointIds 366), (.leaf 3 (Common.fact 362).pointIds 362), (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0078 : B0078.tree = HexagonCover.N7900.SplitData.node0078 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0079
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0070 : Block := .branch 160 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863520570664500254341332505485320, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 334).pointIds 334), B0071, B0078, (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 338).pointIds 338)]
theorem treeEq0070 : B0070.tree = HexagonCover.N7900.SplitData.node0070 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0071
  · exact treeEq0078
  · rfl
  · rfl
  · rfl
  · rfl

def B0086 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 77919046967349146032132, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483407775333885838817569259478581312] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 380).pointIds 380), (.leaf 2 (Common.fact 381).pointIds 381), (.leaf 3 (Common.fact 382).pointIds 382), (.leaf 4 (Common.fact 374).pointIds 374), (.leaf 5 (Common.fact 372).pointIds 372), (.leaf 6 (Common.fact 383).pointIds 383)]
theorem treeEq0086 : B0086.tree = HexagonCover.N7900.SplitData.node0086 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0069 : Block := .branch 86 ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 329).pointIds 329), (.leaf 1 (Common.fact 330).pointIds 330), (.leaf 2 (Common.fact 331).pointIds 331), B0070, (.leaf 4 (Common.fact 332).pointIds 332), (.leaf 5 (Common.fact 333).pointIds 333), B0086]
theorem treeEq0069 : B0069.tree = HexagonCover.N7900.SplitData.node0069 := by
  change Tree.branch (86 : Fin 170) _ = Tree.branch (86 : Fin 170) _
  apply congrArg (Tree.branch (86 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0070
  · rfl
  · rfl
  · exact treeEq0086

theorem accepted0069 : B0069.accepted = true := by decide +kernel
theorem checked0069 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0069 (maskNeeds ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680]) := by
  rw [← treeEq0069]
  exact B0069.sound accepted0069
#print axioms checked0069

def Tip0064_0069 : Block := .tip HexagonCover.N7900.SplitData.node0069 ![604463486268066890776961, 453347182355485940516354, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] checked0069
def B0089 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 386).pointIds 386), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0089 : B0089.tree = HexagonCover.N7900.SplitData.node0089 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0088 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 334).pointIds 334), B0089, (.leaf 2 (Common.fact 385).pointIds 385), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 338).pointIds 338)]
theorem treeEq0088 : B0088.tree = HexagonCover.N7900.SplitData.node0088 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0089
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0087 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 153476910693263469451268, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 384).pointIds 384), B0088, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0087 : B0087.tree = HexagonCover.N7900.SplitData.node0087 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0088
  · rfl
  · rfl
  · rfl

def B0068 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 77928306368183019771908, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 324).pointIds 324), Tip0064_0069, B0087, (.leaf 3 (Common.fact 325).pointIds 325), (.leaf 4 (Common.fact 326).pointIds 326), (.leaf 5 (Common.fact 327).pointIds 327), (.leaf 6 (Common.fact 328).pointIds 328)]
theorem treeEq0068 : B0068.tree = HexagonCover.N7900.SplitData.node0068 := by
  change Tree.branch (77 : Fin 170) _ = Tree.branch (77 : Fin 170) _
  apply congrArg (Tree.branch (77 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0087
  · rfl
  · rfl
  · rfl
  · rfl

def B0093 : Block := .branch 169 ![604463486268066890776961, 453347182355485940516354, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 367).pointIds 367), (.leaf 1 (Common.fact 380).pointIds 380), (.leaf 2 (Common.fact 390).pointIds 390), (.leaf 3 (Common.fact 391).pointIds 391), (.leaf 4 (Common.fact 377).pointIds 377), (.leaf 5 (Common.fact 372).pointIds 372), (.leaf 6 (Common.fact 373).pointIds 373)]
theorem treeEq0093 : B0093.tree = HexagonCover.N7900.SplitData.node0093 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0092 : Block := .branch 77 ![604463486268066890776961, 302231454903657293678082, 2923003274661805836407369740990429765226188511236, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 324).pointIds 324), B0093, (.leaf 2 (Common.fact 389).pointIds 389), (.leaf 3 (Common.fact 325).pointIds 325), (.leaf 4 (Common.fact 326).pointIds 326), (.leaf 5 (Common.fact 327).pointIds 327), (.leaf 6 (Common.fact 328).pointIds 328)]
theorem treeEq0092 : B0092.tree = HexagonCover.N7900.SplitData.node0092 := by
  change Tree.branch (77 : Fin 170) _ = Tree.branch (77 : Fin 170) _
  apply congrArg (Tree.branch (77 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0093
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0091 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 17720707352637197883219678596684931613328182181904, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), B0092, (.leaf 3 (Common.fact 388).pointIds 388), (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0091 : B0091.tree = HexagonCover.N7900.SplitData.node0091 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0092
  · rfl
  · rfl
  · rfl
  · rfl

def B0090 : Block := .branch 162 ![604463486268066890776961, 302231454903657293678082, 75557863725914323425284, 174224571863678988306263738589820825395208, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 344).pointIds 344), (.leaf 1 (Common.fact 345).pointIds 345), (.leaf 2 (Common.fact 346).pointIds 346), (.leaf 3 (Common.fact 387).pointIds 387), B0091, (.leaf 5 (Common.fact 347).pointIds 347), (.leaf 6 (Common.fact 348).pointIds 348)]
theorem treeEq0090 : B0090.tree = HexagonCover.N7900.SplitData.node0090 := by
  change Tree.branch (162 : Fin 170) _ = Tree.branch (162 : Fin 170) _
  apply congrArg (Tree.branch (162 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0091
  · rfl
  · rfl

def B0067 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), B0068, B0090, (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq0067 : B0067.tree = HexagonCover.N7900.SplitData.node0067 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0068
  · exact treeEq0090
  · rfl
  · rfl
  · rfl

def B0101 : Block := .branch 168 ![604463486268066890776961, 1461501637330902918203685134947737923313226221058, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854517163483408092323907148330255900835577920] ![(.leaf 0 (Common.fact 353).pointIds 353), (.leaf 1 (Common.fact 354).pointIds 354), (.leaf 2 (Common.fact 419).pointIds 419), (.leaf 3 (Common.fact 365).pointIds 365), (.leaf 4 (Common.fact 360).pointIds 360), (.leaf 5 (Common.fact 358).pointIds 358), (.leaf 6 (Common.fact 359).pointIds 359)]
theorem treeEq0101 : B0101.tree = HexagonCover.N7900.SplitData.node0101 := by
  change Tree.branch (168 : Fin 170) _ = Tree.branch (168 : Fin 170) _
  apply congrArg (Tree.branch (168 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0100 : Block := .branch 160 ![604463486268066890776961, 302231454903657293678082, 77992833943643984238596, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 334).pointIds 334), B0101, (.leaf 2 (Common.fact 418).pointIds 418), (.leaf 3 (Common.fact 335).pointIds 335), (.leaf 4 (Common.fact 336).pointIds 336), (.leaf 5 (Common.fact 337).pointIds 337), (.leaf 6 (Common.fact 338).pointIds 338)]
theorem treeEq0100 : B0100.tree = HexagonCover.N7900.SplitData.node0100 := by
  change Tree.branch (160 : Fin 170) _ = Tree.branch (160 : Fin 170) _
  apply congrArg (Tree.branch (160 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0101
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0099 : Block := .branch 71 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 320).pointIds 320), (.leaf 1 (Common.fact 321).pointIds 321), B0100, (.leaf 3 (Common.fact 417).pointIds 417), (.leaf 4 (Common.fact 322).pointIds 322), (.leaf 5 (Common.fact 323).pointIds 323), (.leaf 0 [] 0)]
theorem treeEq0099 : B0099.tree = HexagonCover.N7900.SplitData.node0099 := by
  change Tree.branch (71 : Fin 170) _ = Tree.branch (71 : Fin 170) _
  apply congrArg (Tree.branch (71 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0100
  · rfl
  · rfl
  · rfl
  · rfl

def B0098 : Block := .branch 72 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 411).pointIds 411), (.leaf 1 (Common.fact 412).pointIds 412), B0099, (.leaf 3 (Common.fact 413).pointIds 413), (.leaf 4 (Common.fact 414).pointIds 414), (.leaf 5 (Common.fact 415).pointIds 415), (.leaf 6 (Common.fact 416).pointIds 416)]
theorem treeEq0098 : B0098.tree = HexagonCover.N7900.SplitData.node0098 := by
  change Tree.branch (72 : Fin 170) _ = Tree.branch (72 : Fin 170) _
  apply congrArg (Tree.branch (72 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0099
  · rfl
  · rfl
  · rfl
  · rfl

def B0097 : Block := .branch 73 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 405).pointIds 405), (.leaf 1 (Common.fact 406).pointIds 406), B0098, (.leaf 3 (Common.fact 407).pointIds 407), (.leaf 4 (Common.fact 408).pointIds 408), (.leaf 5 (Common.fact 409).pointIds 409), (.leaf 6 (Common.fact 410).pointIds 410)]
theorem treeEq0097 : B0097.tree = HexagonCover.N7900.SplitData.node0097 := by
  change Tree.branch (73 : Fin 170) _ = Tree.branch (73 : Fin 170) _
  apply congrArg (Tree.branch (73 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0098
  · rfl
  · rfl
  · rfl
  · rfl

def B0096 : Block := .branch 74 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522608011663421365877227402380870510182464] ![(.leaf 0 (Common.fact 399).pointIds 399), (.leaf 1 (Common.fact 400).pointIds 400), B0097, (.leaf 3 (Common.fact 401).pointIds 401), (.leaf 4 (Common.fact 402).pointIds 402), (.leaf 5 (Common.fact 403).pointIds 403), (.leaf 6 (Common.fact 404).pointIds 404)]
theorem treeEq0096 : B0096.tree = HexagonCover.N7900.SplitData.node0096 := by
  change Tree.branch (74 : Fin 170) _ = Tree.branch (74 : Fin 170) _
  apply congrArg (Tree.branch (74 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0097
  · rfl
  · rfl
  · rfl
  · rfl

def B0095 : Block := .branch 75 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 2923003448886377699927862958680365044377189376008, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 393).pointIds 393), (.leaf 1 (Common.fact 394).pointIds 394), B0096, (.leaf 3 (Common.fact 395).pointIds 395), (.leaf 4 (Common.fact 396).pointIds 396), (.leaf 5 (Common.fact 397).pointIds 397), (.leaf 6 (Common.fact 398).pointIds 398)]
theorem treeEq0095 : B0095.tree = HexagonCover.N7900.SplitData.node0095 := by
  change Tree.branch (75 : Fin 170) _ = Tree.branch (75 : Fin 170) _
  apply congrArg (Tree.branch (75 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0096
  · rfl
  · rfl
  · rfl
  · rfl

def B0094 : Block := .branch 161 ![604463486268066890776961, 302231454903657293678082, 75631650702209161631748, 174224571863520493293247799005065324290056, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 339).pointIds 339), (.leaf 1 (Common.fact 340).pointIds 340), (.leaf 2 (Common.fact 392).pointIds 392), B0095, (.leaf 4 (Common.fact 341).pointIds 341), (.leaf 5 (Common.fact 342).pointIds 342), (.leaf 6 (Common.fact 343).pointIds 343)]
theorem treeEq0094 : B0094.tree = HexagonCover.N7900.SplitData.node0094 := by
  change Tree.branch (161 : Fin 170) _ = Tree.branch (161 : Fin 170) _
  apply congrArg (Tree.branch (161 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0095
  · rfl
  · rfl
  · rfl

def B0066 : Block := .branch 66 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311353924531193863293834995695680] ![(.leaf 0 (Common.fact 315).pointIds 315), B0067, B0094, (.leaf 3 (Common.fact 316).pointIds 316), (.leaf 4 (Common.fact 317).pointIds 317), (.leaf 5 (Common.fact 318).pointIds 318), (.leaf 6 (Common.fact 319).pointIds 319)]
theorem treeEq0066 : B0066.tree = HexagonCover.N7900.SplitData.node0066 := by
  change Tree.branch (66 : Fin 170) _ = Tree.branch (66 : Fin 170) _
  apply congrArg (Tree.branch (66 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · exact treeEq0067
  · exact treeEq0094
  · rfl
  · rfl
  · rfl
  · rfl

def B0065 : Block := .branch 91 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279311351448651115292533285197447232] ![(.leaf 0 (Common.fact 309).pointIds 309), (.leaf 1 (Common.fact 310).pointIds 310), (.leaf 2 (Common.fact 311).pointIds 311), (.leaf 3 (Common.fact 312).pointIds 312), (.leaf 4 (Common.fact 313).pointIds 313), (.leaf 5 (Common.fact 314).pointIds 314), B0066]
theorem treeEq0065 : B0065.tree = HexagonCover.N7900.SplitData.node0065 := by
  change Tree.branch (91 : Fin 170) _ = Tree.branch (91 : Fin 170) _
  apply congrArg (Tree.branch (91 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0066

def B0064 : Block := .branch 102 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 303).pointIds 303), (.leaf 1 (Common.fact 304).pointIds 304), (.leaf 2 (Common.fact 305).pointIds 305), (.leaf 3 (Common.fact 306).pointIds 306), (.leaf 4 (Common.fact 307).pointIds 307), (.leaf 5 (Common.fact 308).pointIds 308), B0065]
theorem treeEq0064 : B0064.tree = HexagonCover.N7900.SplitData.node0064 := by
  change Tree.branch (102 : Fin 170) _ = Tree.branch (102 : Fin 170) _
  apply congrArg (Tree.branch (102 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0065

theorem accepted0064 : B0064.accepted = true := by decide +kernel
theorem checked0064 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0064 (maskNeeds ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728]) := by
  rw [← treeEq0064]
  exact B0064.sound accepted0064
#print axioms checked0064

def Tip0044_0064 : Block := .tip HexagonCover.N7900.SplitData.node0064 ![604463486268066890776961, 302231454903657293678082, 75567123126748197165060, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] checked0064
def B0063 : Block := .branch 76 ![604463486268066890776961, 302231526961251331606018, 9259400833873745924, 174224571863678988303902555348386002788360, 11874700803313586534923492924246526317860472586256, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 298).pointIds 298), Tip0044_0064, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), (.leaf 6 (Common.fact 302).pointIds 302)]
theorem treeEq0063 : B0063.tree = HexagonCover.N7900.SplitData.node0063 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0062 : Block := .branch 108 ![604463486268066890776961, 302231526961251331606018, 9259400833873745924, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 291).pointIds 291), (.leaf 1 (Common.fact 292).pointIds 292), (.leaf 2 (Common.fact 293).pointIds 293), (.leaf 3 (Common.fact 294).pointIds 294), B0063, (.leaf 5 (Common.fact 295).pointIds 295), (.leaf 6 (Common.fact 296).pointIds 296)]
theorem treeEq0062 : B0062.tree = HexagonCover.N7900.SplitData.node0062 := by
  change Tree.branch (108 : Fin 170) _ = Tree.branch (108 : Fin 170) _
  apply congrArg (Tree.branch (108 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0063
  · rfl
  · rfl

def B0061 : Block := .branch 119 ![604463486268066890776961, 302231526961251331606018, 9259400833873745924, 174224571863678988303902555348386002788360, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 285).pointIds 285), (.leaf 1 (Common.fact 286).pointIds 286), (.leaf 2 (Common.fact 287).pointIds 287), (.leaf 3 (Common.fact 288).pointIds 288), B0062, (.leaf 5 (Common.fact 289).pointIds 289), (.leaf 6 (Common.fact 290).pointIds 290)]
theorem treeEq0061 : B0061.tree = HexagonCover.N7900.SplitData.node0061 := by
  change Tree.branch (119 : Fin 170) _ = Tree.branch (119 : Fin 170) _
  apply congrArg (Tree.branch (119 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0062
  · rfl
  · rfl

def B0060 : Block := .branch 129 ![604463486268066890776961, 302231526961251331606018, 9259400833873745924, 174224571863758216466416819685979546738696, 11874700803313586210404939265819799534704452010000, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 124).pointIds 124), (.leaf 1 (Common.fact 125).pointIds 125), (.leaf 2 (Common.fact 126).pointIds 126), (.leaf 3 (Common.fact 127).pointIds 127), B0061, (.leaf 5 (Common.fact 129).pointIds 129), (.leaf 6 (Common.fact 284).pointIds 284)]
theorem treeEq0060 : B0060.tree = HexagonCover.N7900.SplitData.node0060 := by
  change Tree.branch (129 : Fin 170) _ = Tree.branch (129 : Fin 170) _
  apply congrArg (Tree.branch (129 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0061
  · rfl
  · rfl

def B0059 : Block := .branch 97 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 278).pointIds 278), (.leaf 1 (Common.fact 279).pointIds 279), (.leaf 2 (Common.fact 280).pointIds 280), B0060, (.leaf 4 (Common.fact 281).pointIds 281), (.leaf 5 (Common.fact 282).pointIds 282), (.leaf 6 (Common.fact 283).pointIds 283)]
theorem treeEq0059 : B0059.tree = HexagonCover.N7900.SplitData.node0059 := by
  change Tree.branch (97 : Fin 170) _ = Tree.branch (97 : Fin 170) _
  apply congrArg (Tree.branch (97 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0060
  · rfl
  · rfl
  · rfl

def B0058 : Block := .branch 107 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 272).pointIds 272), (.leaf 1 (Common.fact 273).pointIds 273), (.leaf 2 (Common.fact 274).pointIds 274), B0059, (.leaf 4 (Common.fact 275).pointIds 275), (.leaf 5 (Common.fact 276).pointIds 276), (.leaf 6 (Common.fact 277).pointIds 277)]
theorem treeEq0058 : B0058.tree = HexagonCover.N7900.SplitData.node0058 := by
  change Tree.branch (107 : Fin 170) _ = Tree.branch (107 : Fin 170) _
  apply congrArg (Tree.branch (107 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0059
  · rfl
  · rfl
  · rfl

def B0057 : Block := .branch 118 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 266).pointIds 266), (.leaf 1 (Common.fact 267).pointIds 267), (.leaf 2 (Common.fact 268).pointIds 268), B0058, (.leaf 4 (Common.fact 269).pointIds 269), (.leaf 5 (Common.fact 270).pointIds 270), (.leaf 6 (Common.fact 271).pointIds 271)]
theorem treeEq0057 : B0057.tree = HexagonCover.N7900.SplitData.node0057 := by
  change Tree.branch (118 : Fin 170) _ = Tree.branch (118 : Fin 170) _
  apply congrArg (Tree.branch (118 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0058
  · rfl
  · rfl
  · rfl

def B0056 : Block := .branch 128 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 174224571863599760141388291010792458838024, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 260).pointIds 260), (.leaf 1 (Common.fact 261).pointIds 261), (.leaf 2 (Common.fact 262).pointIds 262), B0057, (.leaf 4 (Common.fact 263).pointIds 263), (.leaf 5 (Common.fact 264).pointIds 264), (.leaf 6 (Common.fact 265).pointIds 265)]
theorem treeEq0056 : B0056.tree = HexagonCover.N7900.SplitData.node0056 := by
  change Tree.branch (128 : Fin 170) _ = Tree.branch (128 : Fin 170) _
  apply congrArg (Tree.branch (128 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0057
  · rfl
  · rfl
  · rfl

def B0055 : Block := .branch 137 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 2854522629279306280846250202374927298384625728] ![(.leaf 0 (Common.fact 255).pointIds 255), (.leaf 1 (Common.fact 256).pointIds 256), (.leaf 2 (Common.fact 257).pointIds 257), B0056, (.leaf 4 (Common.fact 258).pointIds 258), (.leaf 5 (Common.fact 259).pointIds 259), (.leaf 0 [] 0)]
theorem treeEq0055 : B0055.tree = HexagonCover.N7900.SplitData.node0055 := by
  change Tree.branch (137 : Fin 170) _ = Tree.branch (137 : Fin 170) _
  apply congrArg (Tree.branch (137 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact treeEq0056
  · rfl
  · rfl
  · rfl

def B0054 : Block := .branch 151 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 11874701151762729937445925852315397544835100540944, 93536104789177807534223263433152627379965000024096, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 249).pointIds 249), (.leaf 1 (Common.fact 250).pointIds 250), (.leaf 2 (Common.fact 251).pointIds 251), (.leaf 3 (Common.fact 252).pointIds 252), (.leaf 4 (Common.fact 253).pointIds 253), (.leaf 5 (Common.fact 254).pointIds 254), B0055]
theorem treeEq0054 : B0054.tree = HexagonCover.N7900.SplitData.node0054 := by
  change Tree.branch (151 : Fin 170) _ = Tree.branch (151 : Fin 170) _
  apply congrArg (Tree.branch (151 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0055

def B0053 : Block := .branch 163 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177807534223263433152627379965000024096, 27243867386518729678263475937025619132480] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), B0054, (.leaf 5 (Common.fact 247).pointIds 247), (.leaf 6 (Common.fact 248).pointIds 248)]
theorem treeEq0053 : B0053.tree = HexagonCover.N7900.SplitData.node0053 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0054
  · rfl
  · rfl

def B0052 : Block := .branch 113 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177807534223263433152627379965000024096, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 237).pointIds 237), (.leaf 1 (Common.fact 238).pointIds 238), (.leaf 2 (Common.fact 239).pointIds 239), (.leaf 3 (Common.fact 240).pointIds 240), (.leaf 4 (Common.fact 241).pointIds 241), (.leaf 5 (Common.fact 242).pointIds 242), B0053]
theorem treeEq0052 : B0052.tree = HexagonCover.N7900.SplitData.node0052 := by
  change Tree.branch (113 : Fin 170) _ = Tree.branch (113 : Fin 170) _
  apply congrArg (Tree.branch (113 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0053

def B0051 : Block := .branch 87 ![604463486268066890776961, 302231526961251331606018, 46170973748546508804, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177807534223263433152627379965000024096, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 231).pointIds 231), (.leaf 1 (Common.fact 232).pointIds 232), (.leaf 2 (Common.fact 233).pointIds 233), (.leaf 3 (Common.fact 234).pointIds 234), (.leaf 4 (Common.fact 235).pointIds 235), (.leaf 5 (Common.fact 236).pointIds 236), B0052]
theorem treeEq0051 : B0051.tree = HexagonCover.N7900.SplitData.node0051 := by
  change Tree.branch (87 : Fin 170) _ = Tree.branch (87 : Fin 170) _
  apply congrArg (Tree.branch (87 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0052

def B0050 : Block := .branch 65 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177807534223263433152627379965000024096, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 225).pointIds 225), (.leaf 1 (Common.fact 226).pointIds 226), B0051, (.leaf 3 (Common.fact 227).pointIds 227), (.leaf 4 (Common.fact 228).pointIds 228), (.leaf 5 (Common.fact 229).pointIds 229), (.leaf 6 (Common.fact 230).pointIds 230)]
theorem treeEq0050 : B0050.tree = HexagonCover.N7900.SplitData.node0050 := by
  change Tree.branch (65 : Fin 170) _ = Tree.branch (65 : Fin 170) _
  apply congrArg (Tree.branch (65 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0051
  · rfl
  · rfl
  · rfl
  · rfl

def B0049 : Block := .branch 114 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177786765035829293842113257979683143712, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 219).pointIds 219), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0050, (.leaf 6 (Common.fact 224).pointIds 224)]
theorem treeEq0049 : B0049.tree = HexagonCover.N7900.SplitData.node0049 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0050
  · rfl

def B0048 : Block := .branch 141 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177786765035829293842113257979683143712, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B0049, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 218).pointIds 218)]
theorem treeEq0048 : B0048.tree = HexagonCover.N7900.SplitData.node0048 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0049
  · rfl
  · rfl

def B0047 : Block := .branch 150 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 182688053115506591816447190585133387587640197136, 93536104789177786765035829293842113257979683143712, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 100).pointIds 100), (.leaf 1 (Common.fact 101).pointIds 101), (.leaf 2 (Common.fact 102).pointIds 102), (.leaf 3 (Common.fact 103).pointIds 103), B0048, (.leaf 5 (Common.fact 104).pointIds 104), (.leaf 6 (Common.fact 212).pointIds 212)]
theorem treeEq0047 : B0047.tree = HexagonCover.N7900.SplitData.node0047 := by
  change Tree.branch (150 : Fin 170) _ = Tree.branch (150 : Fin 170) _
  apply congrArg (Tree.branch (150 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0048
  · rfl
  · rfl

def B0046 : Block := .branch 157 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 93536104789177786765035829293842113257979683143712, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 207).pointIds 207), (.leaf 1 (Common.fact 208).pointIds 208), (.leaf 2 (Common.fact 209).pointIds 209), (.leaf 3 (Common.fact 210).pointIds 210), B0047, (.leaf 5 (Common.fact 211).pointIds 211), (.leaf 0 [] 0)]
theorem treeEq0046 : B0046.tree = HexagonCover.N7900.SplitData.node0046 := by
  change Tree.branch (157 : Fin 170) _ = Tree.branch (157 : Fin 170) _
  apply congrArg (Tree.branch (157 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0047
  · rfl
  · rfl

def B0045 : Block := .branch 166 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924857866103308203498598301760] ![(.leaf 0 (Common.fact 201).pointIds 201), (.leaf 1 (Common.fact 202).pointIds 202), (.leaf 2 (Common.fact 203).pointIds 203), (.leaf 3 (Common.fact 204).pointIds 204), (.leaf 4 (Common.fact 205).pointIds 205), B0046, (.leaf 6 (Common.fact 206).pointIds 206)]
theorem treeEq0045 : B0045.tree = HexagonCover.N7900.SplitData.node0045 := by
  change Tree.branch (166 : Fin 170) _ = Tree.branch (166 : Fin 170) _
  apply congrArg (Tree.branch (166 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0046
  · rfl

def B0044 : Block := .branch 88 ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0045]
theorem treeEq0044 : B0044.tree = HexagonCover.N7900.SplitData.node0044 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0045

theorem accepted0044 : B0044.accepted = true := by decide +kernel
theorem checked0044 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0044 (maskNeeds ![604463486268066890776961, 302231526961251331606018, 9277485601127405572, 79266848140492005727134572552, 348449143727040986586495598010130648629264, 393248, 27243857001924548381093486858429873520704]) := by
  rw [← treeEq0044]
  exact B0044.sound accepted0044
#print axioms checked0044

def B0133 : Block := .branch 143 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 11692013125891080347554181785328661688211696255040] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), (.leaf 4 (Common.fact 475).pointIds 475), (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 476).pointIds 476)]
theorem treeEq0133 : B0133.tree = HexagonCover.N7900.SplitData.node0133 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0132 : Block := .branch 163 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 243).pointIds 243), (.leaf 1 (Common.fact 244).pointIds 244), (.leaf 2 (Common.fact 245).pointIds 245), (.leaf 3 (Common.fact 246).pointIds 246), (.leaf 4 (Common.fact 474).pointIds 474), (.leaf 5 (Common.fact 247).pointIds 247), B0133]
theorem treeEq0132 : B0132.tree = HexagonCover.N7900.SplitData.node0132 := by
  change Tree.branch (163 : Fin 170) _ = Tree.branch (163 : Fin 170) _
  apply congrArg (Tree.branch (163 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0133

def B0131 : Block := .branch 165 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 349).pointIds 349), (.leaf 1 (Common.fact 350).pointIds 350), (.leaf 2 (Common.fact 351).pointIds 351), (.leaf 3 (Common.fact 352).pointIds 352), (.leaf 4 (Common.fact 473).pointIds 473), B0132, (.leaf 0 [] 0)]
theorem treeEq0131 : B0131.tree = HexagonCover.N7900.SplitData.node0131 := by
  change Tree.branch (165 : Fin 170) _ = Tree.branch (165 : Fin 170) _
  apply congrArg (Tree.branch (165 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0132
  · rfl

def B0130 : Block := .branch 167 ![385, 1538, 6148, 24584, 748288838661871437847327620937232504073968110632976, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 467).pointIds 467), (.leaf 1 (Common.fact 468).pointIds 468), (.leaf 2 (Common.fact 469).pointIds 469), (.leaf 3 (Common.fact 470).pointIds 470), (.leaf 4 (Common.fact 471).pointIds 471), B0131, (.leaf 6 (Common.fact 472).pointIds 472)]
theorem treeEq0130 : B0130.tree = HexagonCover.N7900.SplitData.node0130 := by
  change Tree.branch (167 : Fin 170) _ = Tree.branch (167 : Fin 170) _
  apply congrArg (Tree.branch (167 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0131
  · rfl

def B0129 : Block := .branch 169 ![10141204801825835211973625643393, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 20769187434139310514121985317273632, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), B0130, (.leaf 5 (Common.fact 466).pointIds 466), (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0129 : B0129.tree = HexagonCover.N7900.SplitData.node0129 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0130
  · rfl
  · rfl

def B0128 : Block := .branch 114 ![10141205104057290115630919319937, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 464).pointIds 464), (.leaf 1 (Common.fact 220).pointIds 220), (.leaf 2 (Common.fact 221).pointIds 221), (.leaf 3 (Common.fact 222).pointIds 222), (.leaf 4 (Common.fact 223).pointIds 223), B0129, (.leaf 6 (Common.fact 465).pointIds 465)]
theorem treeEq0128 : B0128.tree = HexagonCover.N7900.SplitData.node0128 := by
  change Tree.branch (114 : Fin 170) _ = Tree.branch (114 : Fin 170) _
  apply congrArg (Tree.branch (114 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0129
  · rfl

def B0137 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 484).pointIds 484)]
theorem treeEq0137 : B0137.tree = HexagonCover.N7900.SplitData.node0137 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0136 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 1430383734999503249937564429831586312219623440, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 477).pointIds 477), B0137, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0136 : B0136.tree = HexagonCover.N7900.SplitData.node0136 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0137
  · rfl

def B0135 : Block := .branch 141 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 27243857001925012608608218876032960692288] ![(.leaf 0 (Common.fact 213).pointIds 213), (.leaf 1 (Common.fact 214).pointIds 214), (.leaf 2 (Common.fact 215).pointIds 215), (.leaf 3 (Common.fact 216).pointIds 216), B0136, (.leaf 5 (Common.fact 217).pointIds 217), (.leaf 6 (Common.fact 460).pointIds 460)]
theorem treeEq0135 : B0135.tree = HexagonCover.N7900.SplitData.node0135 := by
  change Tree.branch (141 : Fin 170) _ = Tree.branch (141 : Fin 170) _
  apply congrArg (Tree.branch (141 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0136
  · rfl
  · rfl

def B0134 : Block := .branch 88 ![10141205406288745019288212996481, 302232391652379786741250, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 27243857001924703123598397530964235911232] ![(.leaf 0 (Common.fact 88).pointIds 88), (.leaf 1 (Common.fact 200).pointIds 200), (.leaf 2 (Common.fact 90).pointIds 90), (.leaf 3 (Common.fact 91).pointIds 91), (.leaf 4 (Common.fact 92).pointIds 92), (.leaf 5 (Common.fact 93).pointIds 93), B0135]
theorem treeEq0134 : B0134.tree = HexagonCover.N7900.SplitData.node0134 := by
  change Tree.branch (88 : Fin 170) _ = Tree.branch (88 : Fin 170) _
  apply congrArg (Tree.branch (88 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0135

def B0127 : Block := .branch 78 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] ![B0128, B0134, (.leaf 2 (Common.fact 195).pointIds 195), (.leaf 3 (Common.fact 196).pointIds 196), (.leaf 4 (Common.fact 197).pointIds 197), (.leaf 5 (Common.fact 198).pointIds 198), (.leaf 6 (Common.fact 463).pointIds 463)]
theorem treeEq0127 : B0127.tree = HexagonCover.N7900.SplitData.node0127 := by
  change Tree.branch (78 : Fin 170) _ = Tree.branch (78 : Fin 170) _
  apply congrArg (Tree.branch (78 : Fin 170))
  funext i
  fin_cases i
  · exact treeEq0128
  · exact treeEq0134
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0140 : Block := .branch 125 ![604462909807314587353473, 1538, 6148, 24584, 98320, 748288838313422294120286634350736906063837462396960, 27243857001924548456651350584344196939840] ![(.leaf 0 (Common.fact 478).pointIds 478), (.leaf 1 (Common.fact 479).pointIds 479), (.leaf 2 (Common.fact 480).pointIds 480), (.leaf 3 (Common.fact 481).pointIds 481), (.leaf 4 (Common.fact 482).pointIds 482), (.leaf 5 (Common.fact 483).pointIds 483), (.leaf 6 (Common.fact 486).pointIds 486)]
theorem treeEq0140 : B0140.tree = HexagonCover.N7900.SplitData.node0140 := by
  change Tree.branch (125 : Fin 170) _ = Tree.branch (125 : Fin 170) _
  apply congrArg (Tree.branch (125 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

def B0139 : Block := .branch 169 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 11498821742992352557354354734334311401619472, 393248, 27243857001924703199156261256878559330368] ![(.leaf 0 (Common.fact 453).pointIds 453), (.leaf 1 (Common.fact 454).pointIds 454), (.leaf 2 (Common.fact 455).pointIds 455), (.leaf 3 (Common.fact 456).pointIds 456), (.leaf 4 (Common.fact 475).pointIds 475), B0140, (.leaf 6 (Common.fact 458).pointIds 458)]
theorem treeEq0139 : B0139.tree = HexagonCover.N7900.SplitData.node0139 := by
  change Tree.branch (169 : Fin 170) _ = Tree.branch (169 : Fin 170) _
  apply congrArg (Tree.branch (169 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0140
  · rfl

def B0138 : Block := .branch 143 ![10141205406288745019288212996481, 936748722493064706, 18482772870728521732, 38685626227668133590622216, 348449143727040986586495598010130648629264, 393248, 27243857001924703199156261256878559330368] ![(.leaf 0 (Common.fact 118).pointIds 118), (.leaf 1 (Common.fact 119).pointIds 119), (.leaf 2 (Common.fact 120).pointIds 120), (.leaf 3 (Common.fact 121).pointIds 121), B0139, (.leaf 5 (Common.fact 122).pointIds 122), (.leaf 6 (Common.fact 485).pointIds 485)]
theorem treeEq0138 : B0138.tree = HexagonCover.N7900.SplitData.node0138 := by
  change Tree.branch (143 : Fin 170) _ = Tree.branch (143 : Fin 170) _
  apply congrArg (Tree.branch (143 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · exact treeEq0139
  · rfl
  · rfl

def B0126 : Block := .branch 76 ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824] ![(.leaf 0 (Common.fact 297).pointIds 297), (.leaf 1 (Common.fact 462).pointIds 462), B0127, (.leaf 3 (Common.fact 299).pointIds 299), (.leaf 4 (Common.fact 300).pointIds 300), (.leaf 5 (Common.fact 301).pointIds 301), B0138]
theorem treeEq0126 : B0126.tree = HexagonCover.N7900.SplitData.node0126 := by
  change Tree.branch (76 : Fin 170) _ = Tree.branch (76 : Fin 170) _
  apply congrArg (Tree.branch (76 : Fin 170))
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact treeEq0127
  · rfl
  · rfl
  · rfl
  · exact treeEq0138

theorem accepted0126 : B0126.accepted = true := by decide +kernel
theorem checked0126 : CheckedWith (fun (_ : Fin 170) => true) Common.allowed Semantics.leafCheck
    HexagonCover.N7900.SplitData.node0126 (maskNeeds ![10141205406288745019288212996481, 443658606491522303490, 18482772870728521732, 38685626227668133590622216, 1427596141849686922044872465047505267031375888, 393248, 38132892743394733954426384968780818677824]) := by
  rw [← treeEq0126]
  exact B0126.sound accepted0126
#print axioms checked0126

end HexagonCover.N7900.SplitAlignedTree.Run0000
